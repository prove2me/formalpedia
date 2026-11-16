-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54n_nonnegative_weighted_caplinear_smooth_extension_grid_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:21:31.524197+00:00
-- url     : https://prove2.me/submissions/55ba3a66-4ad9-4a28-a031-7ea743eeff13

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem solution
    (w : ℝ → ℝ) (b α : ℝ) (hα : 1 ≤ α)
    (S : Finset ℕ) (E X Y G : ℕ → ℝ)
    (hE : ∀ i ∈ S, 0 ≤ E i) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    (∑ i ∈ S, E i * (V (Y i) - V (X i) -
      (if X i ≤ b then G i else 1) * (Y i - X i))) ≤
    (∑ i ∈ S, E i * (U (Y i) - U (X i) -
      (if X i ≤ b then G i else α) * (Y i - X i))) := by
  dsimp
  apply Finset.sum_le_sum
  intro i hi
  have hcore : (if Y i ≤ b then w (Y i) else w b + (Y i - b)) -
      (if X i ≤ b then w (X i) else w b + (X i - b)) -
      (if X i ≤ b then G i else 1) * (Y i - X i) ≤
      (if Y i ≤ b then w (Y i) else w b + α * (Y i - b)) -
      (if X i ≤ b then w (X i) else w b + α * (X i - b)) -
      (if X i ≤ b then G i else α) * (Y i - X i) := by
    by_cases hx : X i ≤ b
    · by_cases hy : Y i ≤ b
      · simp [hx, hy]
      · have hby : 0 ≤ Y i - b := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hy))
        have ha : 0 ≤ α - 1 := sub_nonneg.mpr hα
        have hh : 0 ≤ (α - 1) * (Y i - b) := mul_nonneg ha hby
        simp only [if_pos hx, if_neg hy]
        nlinarith
    · by_cases hy : Y i ≤ b
      · have hby : 0 ≤ b - Y i := sub_nonneg.mpr hy
        have ha : 0 ≤ α - 1 := sub_nonneg.mpr hα
        have hh : 0 ≤ (α - 1) * (b - Y i) := mul_nonneg ha hby
        simp only [if_neg hx, if_pos hy]
        nlinarith
      · simp [hx, hy] <;> nlinarith
  exact mul_le_mul_of_nonneg_left hcore (hE i hi)
