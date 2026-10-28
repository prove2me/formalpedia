-- Prove2me | solution 2 for BitcoinSer.readLE_leBytes
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:53:29.712818+00:00
-- url     : https://prove2.me/submissions/d4446283-6f0a-40a0-b8b4-94333c0b1b24

import Definitions.Def_BitcoinSer
import Theorems.Thm_BitcoinSer_leBytes_length

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

theorem solution (k n : Nat) (rest : Bytes) (h : n < 2 ^ (8 * k)) :
    BitcoinSer.readLE k (BitcoinSer.leBytes k n ++ rest) = some (n, rest) := by
  rw [readLE_append _ _ _ (leBytes_length k n), leVal_leBytes k n h]
