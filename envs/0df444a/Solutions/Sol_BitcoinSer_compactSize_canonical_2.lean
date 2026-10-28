-- Prove2me | solution 2 for BitcoinSer.compactSize_canonical
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:53:56.827602+00:00
-- url     : https://prove2.me/submissions/d02610c2-3d47-4db6-816d-661ab02525f0

import Definitions.Def_BitcoinSer
import Theorems.Thm_BitcoinSer_readLE_leBytes

open BitcoinSer

private theorem leVal_leBytes (k n : Nat) (h : n < 2 ^ (8 * k)) : leVal (leBytes k n) = n := by
  induction k generalizing n with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    simp only [leBytes, leVal, BitVec.toNat_ofNat, Nat.reducePow]
    have h2 : n / 256 < 2 ^ (8 * k) := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
        rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
      omega
    rw [ih _ h2]
    all_goals omega

private theorem leVal_lt (l : Bytes) : leVal l < 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp [leVal]
  | cons b rest ih =>
    simp only [leVal, List.length_cons]
    have hb := b.isLt
    have : 2 ^ (8 * (rest.length + 1)) = 2 ^ (8 * rest.length) * 256 := by
      rw [show 8 * (rest.length + 1) = 8 * rest.length + 8 by omega, Nat.pow_add]
    rw [this]
    all_goals omega

private theorem leBytes_leVal (l : Bytes) : leBytes l.length (leVal l) = l := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons, leBytes, leVal]
    have hb := b.isLt; simp at hb
    have h1 : (b.toNat + 256 * leVal rest) % 256 = b.toNat := by omega
    have h2 : (b.toNat + 256 * leVal rest) / 256 = leVal rest := by omega
    rw [h1, h2, ih, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem readLE_append (l rest : Bytes) (k : Nat) (hk : l.length = k) :
    readLE k (l ++ rest) = some (leVal l, rest) := by
  unfold readLE
  rw [if_neg (by simp; omega), List.take_left' hk, List.drop_left' hk]

/-- A successful fixed-width read determines its input: the bytes are the encoding of the value. -/
private theorem readLE_inv (k : Nat) (s : Bytes) (v : Nat) (rest : Bytes) (h : readLE k s = some (v, rest)) :
    s = leBytes k v ++ rest ∧ v < 2 ^ (8 * k) := by
  unfold readLE at h
  split at h
  · cases h
  · rename_i hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : (s.take k).length = k := by simp; omega
    refine ⟨?_, ?_⟩
    · have e := leBytes_leVal (s.take k)
      rw [ht] at e
      rw [e, List.take_append_drop]
    · have := leVal_lt (s.take k); rwa [ht] at this

private theorem ser8_toNat (n : Nat) (h : n < 256) : (BitVec.ofNat 8 (n % 256)).toNat = n := by
  simp [BitVec.toNat_ofNat]; omega

private theorem leBytes_one (x : Nat) : leBytes 1 x = [BitVec.ofNat 8 (x % 256)] := rfl

private theorem compactSize_roundtrip_gen (rc : Bool) (n : Nat) (rest : Bytes) (h : n < 2 ^ 64)
    (hrc : rc = true → n ≤ MAX_SIZE) :
    readCompactSize rc (writeCompactSize n ++ rest) = some (n, rest) := by
  have hm : (rc && decide (MAX_SIZE < n)) = false := by
    cases rc
    · rfl
    · simp; have := hrc rfl; omega
  have hm' : ¬ (rc = true ∧ MAX_SIZE < n) := by
    cases rc
    · simp
    · simp; have := hrc rfl; omega
  unfold writeCompactSize
  by_cases h1 : n < 253
  · rw [if_pos h1]
    simp only [ser8, leBytes_one, List.cons_append, List.nil_append, readCompactSize]
    rw [ser8_toNat n (by omega)]
    simp [h1, hm]
  · rw [if_neg h1]
    by_cases h2 : n ≤ 0xffff
    · rw [if_pos h2]
      simp only [ser8, ser16, leBytes_one, List.cons_append, List.nil_append, readCompactSize]
      rw [ser8_toNat 253 (by omega), readLE_leBytes 2 n rest (by rw [show (2:Nat)^(8*2) = 65536 from rfl]; omega)]
      simp [h1, hm]
    · rw [if_neg h2]
      by_cases h3 : n ≤ 0xffffffff
      · rw [if_pos h3]
        simp only [ser8, ser32, leBytes_one, List.cons_append, List.nil_append, readCompactSize]
        rw [ser8_toNat 254 (by omega), readLE_leBytes 4 n rest (by rw [show (2:Nat)^(8*4) = 4294967296 from rfl]; omega)]
        simp [hm]
        rw [if_neg (show ¬ n < 65536 by omega)]
        dsimp only
        rw [if_neg hm']
      · rw [if_neg h3]
        simp only [ser8, ser64, leBytes_one, List.cons_append, List.nil_append, readCompactSize]
        rw [ser8_toNat 255 (by omega), readLE_leBytes 8 n rest (by rw [show (2:Nat)^(8*8) = 18446744073709551616 from rfl]; omega)]
        simp [hm]
        rw [if_neg (show ¬ n < 4294967296 by omega)]
        dsimp only
        rw [if_neg hm']

/-- The multi-byte tail of `ReadCompactSize`: a successful read fixes the bytes and the range. -/
private theorem tail_inv (rc : Bool) (k lo : Nat) (tl : Bytes) (n : Nat) (rest : Bytes)
    (h : (match (match readLE k tl with
                 | some (v, r) => if v < lo then none else some (v, r)
                 | none => none) with
          | some (v, r) => if (rc && decide (MAX_SIZE < v)) = true then none else some (v, r)
          | none => none) = some (n, rest)) :
    tl = leBytes k n ++ rest ∧ lo ≤ n ∧ n < 2 ^ (8 * k) ∧ (rc = true → n ≤ MAX_SIZE) := by
  cases hv : readLE k tl with
  | none => rw [hv] at h; simp at h
  | some p =>
    rw [hv] at h
    obtain ⟨v, r⟩ := p
    dsimp only at h
    by_cases hlo : v < lo
    · rw [if_pos hlo] at h; simp at h
    · rw [if_neg hlo] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hrc
        cases h
        have := readLE_inv k tl n rest hv
        refine ⟨this.1, by omega, this.2, fun hr => ?_⟩
        subst hr; simp at hrc; omega

private theorem compactSize_inv (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : readCompactSize rc b = some (n, rest)) :
    b = writeCompactSize n ++ rest ∧ n < 2 ^ 64 ∧ (rc = true → n ≤ MAX_SIZE) := by
  cases b with
  | nil => simp [readCompactSize] at h
  | cons ch tl =>
    unfold readCompactSize at h
    dsimp only at h
    have hch := ch.isLt
    by_cases hc1 : ch.toNat < 253
    · rw [if_pos hc1] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hrc
        cases h
        refine ⟨?_, by omega, fun hr => ?_⟩
        · unfold writeCompactSize
          rw [if_pos hc1]
          simp only [ser8, leBytes_one, List.cons_append, List.nil_append]
          rw [Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
        · subst hr; simp at hrc; omega
    · rw [if_neg hc1] at h
      by_cases hc2 : ch.toNat = 253
      · rw [if_pos hc2] at h
        obtain ⟨e, hlo, hlt, hrc⟩ := tail_inv rc 2 253 tl n rest h
        refine ⟨?_, by omega, hrc⟩
        unfold writeCompactSize
        rw [if_neg (by omega), if_pos (by rw [show (2:Nat)^(8*2) = 65536 from rfl] at hlt; omega)]
        simp only [ser8, ser16, leBytes_one, List.cons_append, List.nil_append, List.append_assoc]
        rw [e, show (BitVec.ofNat 8 (253 % 256)) = ch by rw [← hc2, Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]]
      · rw [if_neg hc2] at h
        by_cases hc3 : ch.toNat = 254
        · rw [if_pos hc3] at h
          obtain ⟨e, hlo, hlt, hrc⟩ := tail_inv rc 4 0x10000 tl n rest h
          rw [show (2:Nat)^(8*4) = 4294967296 from rfl] at hlt
          refine ⟨?_, by omega, hrc⟩
          unfold writeCompactSize
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          simp only [ser8, ser32, leBytes_one, List.cons_append, List.nil_append, List.append_assoc]
          rw [e, show (BitVec.ofNat 8 (254 % 256)) = ch by rw [← hc3, Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]]
        · rw [if_neg hc3] at h
          obtain ⟨e, hlo, hlt, hrc⟩ := tail_inv rc 8 0x100000000 tl n rest h
          rw [show (2:Nat)^(8*8) = 18446744073709551616 from rfl] at hlt
          refine ⟨?_, by omega, hrc⟩
          unfold writeCompactSize
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp only [ser8, ser64, leBytes_one, List.cons_append, List.nil_append, List.append_assoc]
          have hc4 : ch.toNat = 255 := by omega
          rw [e, show (BitVec.ofNat 8 (255 % 256)) = ch by rw [← hc4, Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]]

/-- `ReadCompactSize` accepts only the canonical encoding: a successful read means the input is
exactly `WriteCompactSize` of the value followed by the remainder. -/
theorem solution (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : BitcoinSer.readCompactSize rc b = some (n, rest)) : b = BitcoinSer.writeCompactSize n ++ rest :=
  (compactSize_inv rc b n rest h).1
