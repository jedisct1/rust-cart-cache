extern crate slab;

use slab::Slab;
use std::borrow::Borrow;
use std::cmp::{max, min};
use std::collections::HashMap;
use std::collections::VecDeque;
use std::hash::Hash;
use std::marker::PhantomData;

struct Entry<K, V>
    where K: Eq + Hash
{
    key: K,
    value: V,
    prev: Option<Token>,
    next: Option<Token>,
    is_history: bool,
    is_reference: bool,
    is_longterm: bool,
}

type Token = usize;

pub struct CartCache<K, V>
    where K: Eq + Hash
{
    slab: Slab<Entry<K, V>, Token>,
    map: HashMap<K, Token>,
    t1: VecDeque<Token>,
    t2: VecDeque<Token>,
    b1: XLinkedList<K, V>,
    b2: XLinkedList<K, V>,
    c: usize,
    capacity: usize,
    p: usize,
    q: usize,
    shortterm_count: usize,
    longterm_count: usize,
    inserted: u64,
    evicted: u64,
}

impl<K: Eq + Hash, V> CartCache<K, V> {
    pub fn new(capacity: usize) -> Result<CartCache<K, V>, &'static str> {
        if capacity <= 0 {
            return Err("Cache length cannot be zero");
        }
        let c = capacity / 2;
        let slab = Slab::with_capacity(capacity);
        let map = HashMap::with_capacity(c);
        let t1 = VecDeque::with_capacity(c);
        let t2 = VecDeque::with_capacity(c);
        let b1 = XLinkedList::new();
        let b2 = XLinkedList::new();

        let cache = CartCache {
            slab: slab,
            map: map,
            t1: t1,
            t2: t2,
            b1: b1,
            b2: b2,
            c: c,
            capacity: capacity,
            p: 0,
            q: 0,
            shortterm_count: 0,
            longterm_count: 0,
            inserted: 0,
            evicted: 0,
        };
        Ok(cache)
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn frequent_len(&self) -> usize {
        self.longterm_count + self.b2.len()
    }

    pub fn recent_len(&self) -> usize {
        self.shortterm_count + self.b1.len()
    }

    pub fn inserted(&self) -> u64 {
        self.inserted
    }

    pub fn evicted(&self) -> u64 {
        self.evicted
    }

    pub fn clear(&mut self) {
        self.slab.clear();
        self.map.clear();
        self.t1.clear();
        self.t2.clear();
        self.b1.clear();
        self.b2.clear();
        self.p = 0;
        self.q = 0;
        self.shortterm_count = 0;
        self.longterm_count = 0;
        self.inserted = 0;
        self.evicted = 0;
    }

    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        self.map.contains_key(key)
    }

    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&V>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        match self.map.get(key) {
            Some(&token) => {
                let cached_entry = &mut self.slab[token];
                cached_entry.is_reference = true;
                Some(&cached_entry.value)
            }
            None => None,
        }
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        match self.map.get(key) {
            Some(&token) => {
                let cached_entry = &mut self.slab[token];
                cached_entry.is_reference = true;
                Some(&mut cached_entry.value)
            }
            None => None,
        }
    }

    fn evict_if_full(&mut self, is_history: bool) {
        if self.t1.len() + self.t2.len() >= self.c {
            self.replace();
            if is_history == false && self.b1.len() + self.b2.len() >= self.c + 1 {
                if self.b1.len() > max(0, self.q) || self.b2.is_empty() {
                    let token = self.b1.pop_front(&mut self.slab).expect("Front element vanished");
                    self.map.remove(&self.slab[token].key);
                    self.slab.remove(token);
                } else if !self.b2.is_empty() {
                    let token = self.b2.pop_front(&mut self.slab).expect("Front element vanished");
                    self.map.remove(&self.slab[token].key);
                    self.slab.remove(token);
                }
            }
            self.evicted += 1;
        }
    }

    fn insert_new_entry(&mut self, key: K, value: V)
        where K: Hash + Eq + Clone
    {
        let entry = Entry {
            key: key.clone(),
            value: value,
            prev: None,
            next: None,
            is_history: false,
            is_reference: false,
            is_longterm: false,
        };
        let token = self.slab
            .insert(entry)
            .ok()
            .expect("Slab full");
        self.t1.push_back(token);
        self.shortterm_count += 1;
        self.map.insert(key, token);
        self.inserted += 1;
    }

    fn promote_from_b1(&mut self, token: Token) {
        self.p = min(self.p + max(1, self.shortterm_count / self.b1.len()),
                     self.c);
        {
            let cached_entry = &mut self.slab[token];
            cached_entry.is_history = false;
            cached_entry.is_reference = false;
            cached_entry.is_longterm = true;
            self.longterm_count += 1;
        }
        self.b1.remove(&mut self.slab, token);
        self.t1.push_back(token);
    }

    fn promote_from_b2(&mut self, token: Token) {
        let t = max(1, self.longterm_count / self.b2.len());
        self.p = if self.p > t { self.p - t } else { 0 };
        {
            let cached_entry = &mut self.slab[token];
            cached_entry.is_history = false;
            cached_entry.is_reference = false;
            assert!(cached_entry.is_longterm == true);
            self.longterm_count += 1;
        }
        self.b2.remove(&mut self.slab, token);
        self.t1.push_back(token);
        if self.t2.len() + self.b2.len() + self.t1.len() - self.shortterm_count >= self.c {
            self.q = min(self.q + 1, self.capacity - self.t1.len());
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> bool
        where K: Hash + Eq + Clone
    {
        let (token, is_history, is_longterm) = match self.map.get_mut(&key) {
            Some(&mut token) => {
                let cached_entry = &mut self.slab[token];
                if cached_entry.is_history == false {
                    cached_entry.is_reference = true;
                    cached_entry.value = value;
                    return true;
                }
                (Some(token), cached_entry.is_history, cached_entry.is_longterm)
            }
            None => (None, false, false),
        };
        self.evict_if_full(is_history);
        if is_history == false {
            self.insert_new_entry(key, value);
        } else if is_longterm == false {
            self.promote_from_b1(token.unwrap());
        } else {
            self.promote_from_b2(token.unwrap());
        }
        false
    }

    fn replace_t2(&mut self) {
        loop {
            match self.t2.front() {
                None => break,
                Some(&token) => {
                    if self.slab[token].is_reference != true {
                        break;
                    }
                }
            }
            let token = self.t2.pop_front().expect("Front element vanished");
            let found = &mut self.slab[token];
            found.is_reference = false;
            self.t1.push_back(token);
            if self.t2.len() + self.b2.len() + self.t1.len() - self.shortterm_count >= self.c {
                self.q = min(self.q + 1, self.capacity - self.t1.len())
            }
        }
    }

    fn replace_t1(&mut self) {
        loop {
            match self.t1.front() {
                None => break,
                Some(&token) => {
                    let found = &mut self.slab[token];
                    if !(found.is_longterm == true || found.is_reference == true) {
                        break;
                    }
                }
            }
            let token = self.t1.pop_front().expect("Front element vanished");
            let found = &mut self.slab[token];
            if found.is_reference == true {
                found.is_reference = false;
                self.t1.push_back(token);
                if self.t1.len() >= min(self.p + 1, self.b1.len()) && found.is_longterm == false {
                    assert!(found.is_longterm == false);
                    found.is_longterm = true;
                    self.shortterm_count -= 1;
                    self.longterm_count += 1;
                }
            } else {
                self.t2.push_back(token);
                if self.q > 0 {
                    self.q = max(self.q - 1, self.c - self.t1.len());
                } else {
                    self.q = self.c - self.t1.len();
                }
            }
        }
    }

    fn demote(&mut self) {
        if self.t1.len() >= max(1, self.p) {
            if let Some(token) = self.t1.pop_front() {
                {
                    let demoted = &mut self.slab[token];
                    assert!(demoted.is_history == false);
                    demoted.is_history = true;
                    assert!(demoted.is_longterm == false);
                    self.shortterm_count -= 1;
                }
                self.b1.push_back(&mut self.slab, token);
            }
        } else {
            if let Some(token) = self.t2.pop_front() {
                {
                    let demoted = &mut self.slab[token];
                    assert!(demoted.is_history == false);
                    demoted.is_history = true;
                    assert!(demoted.is_longterm == true);
                    self.longterm_count -= 1;
                }
                self.b2.push_back(&mut self.slab, token);
            }
        }
    }

    fn replace(&mut self) {
        self.replace_t2();
        self.replace_t1();
        self.demote();
    }
}

trait XLinkedNode {
    fn prev(&self) -> Option<Token>;
    fn next(&self) -> Option<Token>;
    fn set_prev(&mut self, prev: Option<Token>);
    fn set_next(&mut self, next: Option<Token>);
}

impl<K, V> XLinkedNode for Entry<K, V>
    where K: Eq + Hash
{
    #[inline]
    fn prev(&self) -> Option<Token> {
        self.prev
    }

    #[inline]
    fn next(&self) -> Option<Token> {
        self.next
    }

    #[inline]
    fn set_prev(&mut self, prev: Option<Token>) {
        self.prev = prev;
    }

    #[inline]
    fn set_next(&mut self, next: Option<Token>) {
        self.next = next;
    }
}

struct XLinkedList<K, V>
    where K: Eq + Hash
{
    head: Option<Token>,
    tail: Option<Token>,
    len: usize,
    phantom_k: PhantomData<K>,
    phantom_v: PhantomData<V>,
}

impl<K, V> XLinkedList<K, V>
    where K: Eq + Hash
{
    fn new() -> Self {
        XLinkedList {
            head: None,
            tail: None,
            len: 0,
            phantom_k: PhantomData,
            phantom_v: PhantomData,
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.len
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    fn clear(&mut self) {
        self.len = 0;
        self.head = None;
        self.tail = None;
    }

    fn remove(&mut self, slab: &mut Slab<Entry<K, V>, Token>, token: Token) {
        let (prev_token, next_token) = {
            let elt = &mut slab[token];
            let prev_token = elt.prev();
            elt.set_prev(None);
            let next_token = elt.next();
            elt.set_next(None);
            (prev_token, next_token)
        };
        if let Some(prev_token) = prev_token {
            slab[prev_token].set_next(next_token);
        } else {
            self.head = next_token;
        }
        if let Some(next_token) = next_token {
            slab[next_token].set_prev(prev_token);
        } else {
            self.tail = prev_token;
        }
        self.len -= 1;
    }

    fn push_back(&mut self, slab: &mut Slab<Entry<K, V>, Token>, token: Token) {
        {
            let elt = &mut slab[token];
            elt.set_prev(self.tail);
            elt.set_next(None);
        }
        if let Some(tail_token) = self.tail {
            slab[tail_token].set_next(Some(token));
        }
        self.tail = Some(token);
        self.head = self.head.or(self.tail);
        self.len += 1;
    }

    pub fn pop_front(&mut self, slab: &mut Slab<Entry<K, V>, Token>) -> Option<Token> {
        let head_token = self.head;
        if let Some(head_token) = head_token {
            let new_head_token = {
                let former_head = &mut slab[head_token];
                let next_token = former_head.next();
                former_head.set_next(None);
                next_token
            };
            match new_head_token {
                None => self.clear(),
                Some(new_head_token) => {
                    slab[new_head_token].set_prev(None);
                    self.head = Some(new_head_token);
                    self.len -= 1;
                }
            }
        }
        head_token
    }
}

#[cfg(test)]
mod tests {
    extern crate rand;
    use self::rand::Rng;
    use CartCache;

    #[test]
    fn random_inserts() {
        let count = 1_000_000;
        let mut cached: u64 = 0;
        let mut cache: CartCache<u8, u8> = CartCache::new(128).unwrap();
        let mut rng = rand::weak_rng();

        for _ in 0..count {
            let key: u8 = rng.gen();
            cache.insert(key, key);
            let key: u8 = rng.gen();
            if cache.get(&key).is_some() {
                cached += 1;
            }
        }
        assert!(cached > count / 3);
    }
}
