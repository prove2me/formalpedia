-- Prove2me | solution 1 for DetANN.sylvester_hadamard
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T03:02:00.066987+00:00
-- url     : https://prove2.me/submissions/ee1f67a8-8bec-46b6-8e35-1edac4dfd603

import Mathlib
import Definitions.Def_DetANN_Sylvester

open DetANN

namespace DetANNSylvAux

lemma bitDot_succ (k j r : ℕ) :
    bitDot (k + 1) j r = bitDot k (j % 2 ^ k) (r % 2 ^ k) +
      (if j.testBit k && r.testBit k then 1 else 0) := by
  unfold bitDot
  rw [Finset.range_add_one, Finset.filter_insert]
  have hfil : ((Finset.range k).filter fun b => j.testBit b && r.testBit b) =
      (Finset.range k).filter fun b => (j % 2 ^ k).testBit b && (r % 2 ^ k).testBit b := by
    refine Finset.filter_congr fun b hb => ?_
    have hb' : b < k := Finset.mem_range.mp hb
    simp [Nat.testBit_mod_two_pow, hb']
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (by simp), hfil]
  · rw [hfil]; simp

lemma lo_mod (k : ℕ) (i : Fin (2 ^ k)) : ((loIdx k i : ℕ)) % 2 ^ k = i := Nat.mod_eq_of_lt i.2
lemma hi_mod (k : ℕ) (i : Fin (2 ^ k)) : ((hiIdx k i : ℕ)) % 2 ^ k = i := by
  simp only [hiIdx]; rw [Nat.add_mod_left, Nat.mod_eq_of_lt i.2]
lemma lo_bit (k : ℕ) (i : Fin (2 ^ k)) : (loIdx k i : ℕ).testBit k = false :=
  Nat.testBit_lt_two_pow i.2
lemma hi_bit (k : ℕ) (i : Fin (2 ^ k)) : (hiIdx k i : ℕ).testBit k = true := by
  simp only [hiIdx]; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow i.2]; rfl

lemma syl_entry (k : ℕ) (a b : Fin (2 ^ (k + 1))) (a' b' : Fin (2 ^ k))
    (ha : (a : ℕ) % 2 ^ k = a') (hb : (b : ℕ) % 2 ^ k = b') :
    sylvester (k + 1) a b = (if (a : ℕ).testBit k && (b : ℕ).testBit k then -1 else 1) *
      sylvester k a' b' := by
  simp only [sylvester]
  rw [bitDot_succ, ha, hb, pow_add]
  split_ifs <;> ring

lemma s_ll (k : ℕ) (a b : Fin (2 ^ k)) : sylvester (k + 1) (loIdx k a) (loIdx k b) = sylvester k a b := by
  rw [syl_entry k _ _ a b (lo_mod k a) (lo_mod k b), lo_bit, lo_bit]; simp
lemma s_lh (k : ℕ) (a b : Fin (2 ^ k)) : sylvester (k + 1) (loIdx k a) (hiIdx k b) = sylvester k a b := by
  rw [syl_entry k _ _ a b (lo_mod k a) (hi_mod k b), lo_bit, hi_bit]; simp
lemma s_hl (k : ℕ) (a b : Fin (2 ^ k)) : sylvester (k + 1) (hiIdx k a) (loIdx k b) = sylvester k a b := by
  rw [syl_entry k _ _ a b (hi_mod k a) (lo_mod k b), hi_bit, lo_bit]; simp
lemma s_hh (k : ℕ) (a b : Fin (2 ^ k)) : sylvester (k + 1) (hiIdx k a) (hiIdx k b) = -sylvester k a b := by
  rw [syl_entry k _ _ a b (hi_mod k a) (hi_mod k b), hi_bit, hi_bit]; simp

lemma sum_split {M : Type*} [AddCommMonoid M] (k : ℕ) (f : Fin (2 ^ (k + 1)) → M) :
    ∑ x, f x = ∑ i : Fin (2 ^ k), (f (loIdx k i) + f (hiIdx k i)) := by
  have e : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
  rw [← Equiv.sum_comp (finCongr e) f, Fin.sum_univ_add, ← Finset.sum_add_distrib]
  rfl

lemma lo_or_hi (k : ℕ) (a : Fin (2 ^ (k + 1))) : (∃ a', a = loIdx k a') ∨ ∃ a', a = hiIdx k a' := by
  by_cases h : (a : ℕ) < 2 ^ k
  · exact Or.inl ⟨⟨a, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨a - 2 ^ k, ?_⟩, Fin.ext ?_⟩
    · have h2 : (a : ℕ) < 2 ^ k * 2 := lt_of_lt_of_eq a.2 (pow_succ 2 k)
      omega
    · simp only [hiIdx]; omega

lemma lo_inj (k : ℕ) {a b : Fin (2 ^ k)} : loIdx k a = loIdx k b ↔ a = b := by
  simp [loIdx, Fin.ext_iff]
lemma hi_inj (k : ℕ) {a b : Fin (2 ^ k)} : hiIdx k a = hiIdx k b ↔ a = b := by
  simp [hiIdx, Fin.ext_iff]
lemma lo_ne_hi (k : ℕ) (a b : Fin (2 ^ k)) : loIdx k a ≠ hiIdx k b := by
  intro h; have := congrArg Fin.val h; simp [loIdx, hiIdx] at this; omega

lemma orth : ∀ (k : ℕ) (a b : Fin (2 ^ k)),
    ∑ x, sylvester k x a * sylvester k x b = if a = b then (2 ^ k : ℝ) else 0
  | 0, a, b => by
    have : a = b := Fin.ext (by have := a.2; have := b.2; simp at *)
    subst this; simp [sylvester, bitDot]
  | k + 1, a, b => by
    rw [sum_split]
    rcases lo_or_hi k a with ⟨a', rfl⟩ | ⟨a', rfl⟩ <;> rcases lo_or_hi k b with ⟨b', rfl⟩ | ⟨b', rfl⟩
    · simp only [s_ll, s_hl, ← two_mul, ← Finset.mul_sum, orth k a' b', lo_inj]
      split_ifs <;> ring
    · simp only [s_ll, s_hl, s_lh, s_hh, if_neg (lo_ne_hi k a' b')]
      exact (Finset.sum_congr rfl fun x _ => by ring).trans Finset.sum_const_zero
    · simp only [s_ll, s_hl, s_lh, s_hh, if_neg (lo_ne_hi k b' a').symm]
      exact (Finset.sum_congr rfl fun x _ => by ring).trans Finset.sum_const_zero
    · simp only [s_lh, s_hh, neg_mul_neg, ← two_mul, ← Finset.mul_sum, orth k a' b', hi_inj]
      split_ifs <;> ring

end DetANNSylvAux

open DetANNSylvAux in
theorem solution (k : ℕ) :
    (∀ j r, sylvester k j r = 1 ∨ sylvester k j r = -1) ∧
    (sylvester k).transpose * sylvester k = ((2 ^ k : ℕ) : ℝ) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) ∧
    ∀ (z : Fin (2 ^ (k + 1)) → ℝ) (i : Fin (2 ^ k)),
      (sylvester (k + 1)).mulVec z (loIdx k i) =
          (sylvester k).mulVec (fun r => z (loIdx k r) + z (hiIdx k r)) i ∧
      (sylvester (k + 1)).mulVec z (hiIdx k i) =
          (sylvester k).mulVec (fun r => z (loIdx k r) - z (hiIdx k r)) i := by
  refine ⟨fun j r => neg_one_pow_eq_or ℝ _, ?_, fun z i => ⟨?_, ?_⟩⟩
  · ext a b
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    rw [orth k a b]
    split_ifs <;> simp
  · simp only [Matrix.mulVec, dotProduct]
    rw [sum_split]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [s_ll, s_lh]; ring
  · simp only [Matrix.mulVec, dotProduct]
    rw [sum_split]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [s_hl, s_hh]; ring
