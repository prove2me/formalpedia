-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54m_upper_caplinear_smooth_extension_one_sided_Taylor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:21:06.556197+00:00
-- url     : https://prove2.me/submissions/13b47c21-488a-4f6b-9f8c-9447063a4a83

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (w : ℝ → ℝ) (b α g x y : ℝ) (hα : 1 ≤ α) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    let gv : ℝ := if x ≤ b then g else 1
    let gu : ℝ := if x ≤ b then g else α
    V y - V x - gv * (y - x) ≤ U y - U x - gu * (y - x) := by
  dsimp
  by_cases hx : x ≤ b
  · by_cases hy : y ≤ b
    · simp [hx, hy]
    · have hby : 0 ≤ y - b := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hy))
      have ha : 0 ≤ α - 1 := sub_nonneg.mpr hα
      have hh : 0 ≤ (α - 1) * (y - b) := mul_nonneg ha hby
      simp only [if_pos hx, if_neg hy]
      nlinarith
  · by_cases hy : y ≤ b
    · have hby : 0 ≤ b - y := sub_nonneg.mpr hy
      have ha : 0 ≤ α - 1 := sub_nonneg.mpr hα
      have hh : 0 ≤ (α - 1) * (b - y) := mul_nonneg ha hby
      simp only [if_neg hx, if_pos hy]
      nlinarith
    · simp [hx, hy] <;> nlinarith
