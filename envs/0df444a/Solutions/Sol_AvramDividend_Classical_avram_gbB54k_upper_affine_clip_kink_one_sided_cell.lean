-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54k_upper_affine_clip_kink_one_sided_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:06:03.02281+00:00
-- url     : https://prove2.me/submissions/d60df8d3-86c9-404f-94de-81dd3451207f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (b α x y : ℝ) (hα : 1 ≤ α) :
    let V : ℝ → ℝ := fun z => if z ≤ b then α * z else α * b + (z - b)
    let G : ℝ := if x ≤ b then α else 1
    V y - V x - G * (y - x) ≤ 0 := by
  dsimp
  by_cases hx : x ≤ b
  · by_cases hy : y ≤ b
    · simp [hx, hy]
      nlinarith
    · have hby : 0 ≤ y - b := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hy))
      have ha : 1 - α ≤ 0 := sub_nonpos.mpr hα
      have hh : (1 - α) * (y - b) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ha hby
      simp [hx, hy]
      nlinarith
  · by_cases hy : y ≤ b
    · have hby : y - b ≤ 0 := sub_nonpos.mpr hy
      have ha : 0 ≤ α - 1 := sub_nonneg.mpr hα
      have hh : (α - 1) * (y - b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha hby
      simp [hx, hy]
      nlinarith
    · simp [hx, hy]
