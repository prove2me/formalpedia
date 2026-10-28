-- Prove2me | solution 1 for BitcoinSer.compactSize_canonical
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:06:58.365426+00:00
-- url     : https://prove2.me/submissions/d6d400b6-0ed3-4606-a17b-1469456069e5

import Definitions.Def_BitcoinSer
open BitcoinSer

theorem C_len (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem C_val (k n : Nat) (h : n < 2 ^ (8 * k)) : leVal (leBytes k n) = n := by
  induction k generalizing n with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    simp only [leBytes, leVal]
    have : n / 256 < 2 ^ (8 * k) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have : 2 ^ (8 * (k+1)) = 2 ^ (8*k) * 256 := by rw [show 8*(k+1) = 8*k+8 by omega, Nat.pow_add]
      omega
    rw [ih _ this]
    simp [BitVec.toNat_ofNat]
    omega

theorem C_read (k n : Nat) (rest : Bytes) (h : n < 2 ^ (8 * k)) :
    readLE k (leBytes k n ++ rest) = some (n, rest) := by
  simp [readLE, C_len, C_val k n h]

theorem C_rt (rc : Bool) (n : Nat) (rest : Bytes) (h : n < 2 ^ 64) (hr : rc = true → n ≤ MAX_SIZE) :
    readCompactSize rc (writeCompactSize n ++ rest) = some (n, rest) := by
  unfold writeCompactSize
  by_cases h1 : n < 253
  · simp only [h1, if_true, ser8, leBytes, List.cons_append, List.nil_append, readCompactSize]
    have : (BitVec.ofNat 8 (n % 256)).toNat = n := by simp [BitVec.toNat_ofNat]; omega
    simp only [this, h1, if_true]
    cases rc <;> simp_all
  by_cases h2 : n ≤ 0xffff
  · simp only [h1, h2, if_true, if_false, ser8, ser16, leBytes, List.cons_append, List.nil_append,
      readCompactSize]
    have := C_read 2 n rest (by omega)
    simp only [leBytes, List.cons_append, List.nil_append] at this
    rw [this]
    have e : ¬ n < 253 := h1
    simp only [e, if_false]
    have hm : rc = true → ¬ MAX_SIZE < n := fun hh => Nat.not_lt.2 (hr hh)
    cases rc <;> simp_all
  by_cases h3 : n ≤ 0xffffffff
  · simp only [h1, h2, h3, if_true, if_false, ser8, ser32, leBytes, List.cons_append, List.nil_append,
      readCompactSize]
    have := C_read 4 n rest (by omega)
    simp only [leBytes, List.cons_append, List.nil_append] at this
    rw [this]
    have e : ¬ n < 0x10000 := by omega
    simp only [e, if_false]
    have hm : rc = true → ¬ MAX_SIZE < n := fun hh => Nat.not_lt.2 (hr hh)
    cases rc <;> simp_all
  · simp only [h1, h2, h3, if_false, ser8, ser64, leBytes, List.cons_append, List.nil_append,
      readCompactSize]
    have := C_read 8 n rest (by omega)
    simp only [leBytes, List.cons_append, List.nil_append] at this
    rw [this]
    have e : ¬ n < 0x100000000 := by omega
    simp only [e, if_false]
    have hm : rc = true → ¬ MAX_SIZE < n := fun hh => Nat.not_lt.2 (hr hh)
    cases rc <;> simp_all


theorem C_vlt (l : Bytes) : leVal l < 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp [leVal]
  | cons b l ih =>
    simp only [leVal, List.length_cons]
    have hb := b.isLt
    rw [show 8 * (l.length + 1) = 8 * l.length + 8 by omega, Nat.pow_add]
    have : 2 ^ 8 = 256 := rfl
    omega

theorem C_inv (l : Bytes) : leBytes l.length (leVal l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [leBytes, leVal, List.length_cons]
    have hb := b.isLt
    have e1 : (b.toNat + 256 * leVal l) % 256 = b.toNat := by omega
    have e2 : (b.toNat + 256 * leVal l) / 256 = leVal l := by omega
    rw [e1, e2, ih]
    simp

theorem C_readinv (k : Nat) (s : Bytes) (v : Nat) (r : Bytes) (h : readLE k s = some (v, r)) :
    s = leBytes k v ++ r ∧ v < 2 ^ (8 * k) := by
  unfold readLE at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl : (s.take k).length = k := by simp; omega
    refine ⟨?_, ?_⟩
    · have := C_inv (s.take k)
      rw [hl] at this
      rw [this, List.take_append_drop]
    · have := C_vlt (s.take k); rwa [hl] at this

theorem C_range_can (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : readCompactSize rc b = some (n, rest)) :
    (n < 2 ^ 64 ∧ (rc = true → n ≤ MAX_SIZE)) ∧ b = writeCompactSize n ++ rest := by
  cases b with
  | nil => simp [readCompactSize] at h
  | cons ch r0 =>
    have hch : ch.toNat < 256 := ch.isLt
    have hfin : ∀ (v : Nat) (r : Bytes), (match some (v, r) with
        | some (v, r) => if rc && decide (MAX_SIZE < v) then none else some (v, r)
        | none => none) = some (n, rest) → v = n ∧ r = rest ∧ (rc = true → n ≤ MAX_SIZE) := by
      intro v r hv
      cases rc <;> simp at hv
      · exact ⟨hv.1, hv.2, by simp⟩
      · obtain ⟨h1, h2, h3⟩ := hv; subst h2; subst h3; exact ⟨rfl, rfl, fun _ => by omega⟩
    simp only [readCompactSize] at h
    by_cases c1 : ch.toNat < 253
    · simp only [c1, if_true] at h
      obtain ⟨rfl, rfl, hr⟩ := hfin _ _ h
      refine ⟨⟨by omega, hr⟩, ?_⟩
      simp [writeCompactSize, c1, ser8, leBytes]
      apply BitVec.eq_of_toNat_eq; simp; omega
    by_cases c253 : ch.toNat = 253
    · simp only [c1, c253, if_true, if_false] at h
      cases hr : readLE 2 r0 with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨v, r⟩ := p
        simp only [hr] at h
        by_cases hv : v < 253
        · simp [hv] at h
        simp only [hv, if_false] at h
        obtain ⟨rfl, rfl, hrc⟩ := hfin _ _ h
        obtain ⟨e, hlt⟩ := C_readinv _ _ _ _ hr
        refine ⟨⟨by omega, hrc⟩, ?_⟩
        subst e
        have hch' : ch = BitVec.ofNat 8 253 := by apply BitVec.eq_of_toNat_eq; simp; omega
        subst hch'
        have h1 : ¬ v < 253 := hv
        have h2 : v ≤ 0xffff := by simp at hlt; omega
        have h3 : True := trivial
        simp [writeCompactSize, ser16, ser8, h1, h2, h3, hv]
        simp [leBytes]
    by_cases c254 : ch.toNat = 254
    · simp only [c1, c253, c254, if_true, if_false] at h
      cases hr : readLE 4 r0 with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨v, r⟩ := p
        simp only [hr] at h
        by_cases hv : v < 0x10000
        · simp [hv] at h
        simp only [hv, if_false] at h
        obtain ⟨rfl, rfl, hrc⟩ := hfin _ _ h
        obtain ⟨e, hlt⟩ := C_readinv _ _ _ _ hr
        refine ⟨⟨by omega, hrc⟩, ?_⟩
        subst e
        have hch' : ch = BitVec.ofNat 8 254 := by apply BitVec.eq_of_toNat_eq; simp; omega
        subst hch'
        have h1 : ¬ v < 253 := by omega
        have h2 : ¬ v ≤ 0xffff := by omega
        have h3 : v ≤ 0xffffffff := by simp at hlt; omega
        simp [writeCompactSize, ser32, ser8, h1, h2, h3, hv]
        simp [leBytes]
    simp only [c1, c253, c254, if_false] at h
    cases hr : readLE 8 r0 with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨v, r⟩ := p
      simp only [hr] at h
      by_cases hv : v < 0x100000000
      · simp [hv] at h
      simp only [hv, if_false] at h
      obtain ⟨rfl, rfl, hrc⟩ := hfin _ _ h
      obtain ⟨e, hlt⟩ := C_readinv _ _ _ _ hr
      refine ⟨⟨by simpa using hlt, hrc⟩, ?_⟩
      subst e
      have hch' : ch = BitVec.ofNat 8 255 := by apply BitVec.eq_of_toNat_eq; simp; omega
      subst hch'
      have h1 : ¬ v < 253 := by omega
      have h2 : ¬ v ≤ 0xffff := by omega
      have h3 : ¬ v ≤ 0xffffffff := by omega
      simp [writeCompactSize, ser64, ser8, h1, h2, h3]
      simp [leBytes]

open BitcoinSer in
theorem solution (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : BitcoinSer.readCompactSize rc b = some (n, rest)) : b = BitcoinSer.writeCompactSize n ++ rest :=
  (C_range_can rc b n rest h).2
