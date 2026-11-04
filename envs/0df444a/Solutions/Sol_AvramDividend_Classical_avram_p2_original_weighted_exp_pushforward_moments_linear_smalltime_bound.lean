-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:10:07.268428+00:00
-- url     : https://prove2.me/submissions/b5a164dd-15e6-4b17-94e5-d1e7a980b14e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_pushforward_moment_formula
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every polynomial moment of the fourth-weighted original
exponential pushforward is O(h), on the original probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))) ≤
          ENNReal.ofReal (C * h) := by
  obtain ⟨C, hC, hb⟩ :=
    avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound
      X (k : ℝ) (by positivity)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with h hbound
  rw [avram_p2_original_fourth_weighted_exp_pushforward_moment_formula]
  calc
    (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) *
      ENNReal.ofReal ((Real.exp (X.X (Real.toNNReal h) ω)) ^ k) ∂P) =
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((k : ℝ) *
      X.X (Real.toNNReal h) ω) *
      (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P) := by
      congr 1
      funext ω
      rw [Real.exp_nat_mul]
      rw [ENNReal.ofReal_mul (pow_nonneg (le_of_lt (Real.exp_pos _)) k)]
      exact mul_comm _ _
    _ ≤ ENNReal.ofReal (C * h) := hbound
