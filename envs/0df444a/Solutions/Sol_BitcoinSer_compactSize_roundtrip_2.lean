-- Prove2me | solution 2 for BitcoinSer.compactSize_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:53:55.908572+00:00
-- url     : https://prove2.me/submissions/7be33e7d-1fc7-45ca-b24a-85e92071c867

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

theorem solution (n : Nat) (rest : Bytes) (h : n < 2 ^ 64) :
    BitcoinSer.readCompactSize false (BitcoinSer.writeCompactSize n ++ rest) = some (n, rest) :=
  compactSize_roundtrip_gen false n rest h (by simp)
