-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01b_actual_horizon_killed_reward_two_way_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:03:09.703267+00:00
-- url     : https://prove2.me/submissions/7de1dd5e-b632-4651-a5f4-de57034b1ca9

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_two_sided_strict_exit_no_finite_tie

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a)
    (T : ℝ≥0) (ω : Ω) :
    (let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
     let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
     (if (T : ℝ≥0∞) < D then
        if min U D < ⊤ then
          Real.exp (-(q * ((min (min U D).toNNReal T) : ℝ))) *
            W (x + X.X (min (min U D).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else if D < U then 0
      else Real.exp (-(q * (U.toNNReal : ℝ))) *
        W (x + X.X U.toNNReal ω)) =
     (if U < D ∧ U.toNNReal ≤ T then
        Real.exp (-(q * (U.toNNReal : ℝ))) *
          W (x + X.X U.toNNReal ω) else 0) +
     (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
        Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω) else 0)) := by
  have tie := chat04_two_sided_strict_exit_no_finite_tie X a x ha hxa ω
  dsimp only
  generalize twoSidedExitUpTime X (a - x) ω = U at tie ⊢
  generalize twoSidedExitDownTime X (-x) ω = D at tie ⊢
  induction U using ENNReal.recTopCoe <;> induction D using ENNReal.recTopCoe
  · simp
  · rename_i d
    simp only [ENNReal.coe_lt_coe, ENNReal.toNNReal_top, min_top_left, ENNReal.coe_lt_top, if_true,
      ENNReal.toNNReal_coe, not_top_lt, false_and, if_false, zero_add, and_true, true_and]
    rcases lt_or_ge T d with h | h
    · simp [h, h.le, min_eq_right h.le]
    · simp [not_lt.mpr h]
  · rename_i u
    simp only [ENNReal.coe_lt_coe, ENNReal.toNNReal_top, min_top_right, ENNReal.coe_lt_top, if_true,
      ENNReal.toNNReal_coe, lt_top_iff_ne_top, ne_eq, not_true_eq_false, false_and, if_false, add_zero, and_true,
      true_and, ENNReal.coe_ne_top, not_false_eq_true]
    rcases lt_or_ge T u with h | h
    · simp [h, h.le, min_eq_right h.le, not_le.mpr h]
    · simp [not_lt.mpr h, h, min_eq_left h]
  · rename_i u d
    have tie' : u ≠ d := fun h => ENNReal.coe_ne_top (tie (congrArg _ h))
    simp only [ENNReal.coe_lt_coe, ENNReal.toNNReal_coe, ← ENNReal.coe_min, ENNReal.coe_lt_top, if_true]
    rcases lt_or_ge T d with h1 | h1 <;> rcases lt_or_ge T u with h2 | h2 <;> rcases lt_or_ge u d with h3 | h3
    all_goals simp only [h1, h2, h3, not_lt.mpr, not_le.mpr, if_true, if_false, true_and, and_true, false_and, and_false, zero_add, add_zero, le_of_lt, min_eq_left, min_eq_right]
    all_goals first | (exfalso; order) | (rw [if_pos (lt_of_le_of_ne h3 (Ne.symm tie'))]) | (rw [min_eq_right (NNReal.coe_le_coe.mpr h2.le)]) | (rw [min_eq_right (NNReal.coe_le_coe.mpr h1.le)]) | (rw [min_eq_left (NNReal.coe_le_coe.mpr h2)])
