-- Prove2me | solution 1 for BlockCycleRotation.bcRotate_eq_rotate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:36:30.510007+00:00
-- url     : https://prove2.me/submissions/cd4ed291-4146-4c02-8b35-45f81a563783

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_Rotate
import Theorems.Thm_BlockCycleRotation_rotate_block_step
import Mathlib

variable {α : Type*}

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **Correctness of the block cycle algorithm.**  For `k ≤ l.length`,
`bcRotate l k` is the rotation of `l` by `k`. -/
theorem solution : ∀ (l : List α) (k : ℕ), k ≤ l.length →
    bcRotate l k = l.rotate k:= by
  intro l k
  induction l, k using bcRotate.induct with
  | case1 l =>
    intro _
    rw [bcRotate]
    simp
  | case2 l k h0 h1 =>
    intro hk
    have hkl : k = l.length := le_antisymm hk h1
    rw [bcRotate, if_neg h0, if_pos h1, hkl, List.rotate_length]
  | case3 l k h0 h1 h2 ih =>
    intro hk
    rw [bcRotate, if_neg h0, if_neg h1, if_pos h2]
    have hkpos : 0 < k := Nat.pos_of_ne_zero h0
    have hmn : l.length / k * k ≤ l.length := Nat.div_mul_le_self _ _
    have hb : 1 ≤ l.length / k := (Nat.one_le_div_iff hkpos).2 hk
    have hkm : k ≤ l.length / k * k := by
      calc k = 1 * k := (one_mul k).symm
        _ ≤ l.length / k * k := Nat.mul_le_mul_right k hb
    have hsub : k ≤ (List.take k (List.take (l.length / k * k) l) ++
        List.drop (l.length / k * k) l).length := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    rw [ih hsub]
    exact (rotate_block_step l hkpos hk).symm
  | case4 l k h0 h1 h2 ih =>
    intro hk
    rw [bcRotate, if_neg h0, if_neg h1, if_neg h2]
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    have hkn : k < l.length := by omega
    have hrev : l.length - k ≤ l.reverse.length := by simp
    rw [ih hrev]
    have hrr := List.reverse_rotate l k
    rw [Nat.mod_eq_of_lt hkn] at hrr
    rw [← hrr, List.reverse_reverse]
