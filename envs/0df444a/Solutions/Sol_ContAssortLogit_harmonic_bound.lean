-- Prove2me | solution 1 for ContAssortLogit.harmonic_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:15:28.260824+00:00
-- url     : https://prove2.me/submissions/4ec67e71-66f6-4d91-ae9b-309e4e814127

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

private lemma harmonic_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Finset.Icc 1 n, 1 / (t : ℝ) ≤ 1 + Real.log n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
    have hnp : (0 : ℝ) < n + 1 := by positivity
    have hratio : 0 < ((n : ℝ) + 1) / n := div_pos hnp hn0
    have hl := Real.one_sub_inv_le_log_of_pos hratio
    rw [Real.log_div hnp.ne' hn0.ne'] at hl
    have hi : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by
      field_simp
      <;> ring
    rw [hi] at hl
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

theorem solution (β : ℝ) (hβ : 0 ≤ β) (T : ℕ) (hT : 2 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T, 1 / ((t : ℝ) + β) ≤ 3 * Real.log T := by
  have hsum : ∑ t ∈ Finset.Icc 1 T, 1 / ((t : ℝ) + β) ≤
      ∑ t ∈ Finset.Icc 1 T, 1 / (t : ℝ) := by
    apply Finset.sum_le_sum
    intro t ht
    have ht0 : (0 : ℝ) < t := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (Finset.mem_Icc.mp ht).1)
    exact one_div_le_one_div_of_le ht0 (le_add_of_nonneg_right hβ)
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hlT : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hmain := harmonic_log T (by omega)
  linarith

#print axioms solution
