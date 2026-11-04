-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:04:40.031993+00:00
-- url     : https://prove2.me/submissions/1ac6869b-b04e-46db-b894-b65960df48d4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_linear_smalltime_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- At every nonnegative exponential tilt, original source weighted ENNReal
mass is O(h), allowing direct finite-measure mass and tail estimates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫⁻ ω, ENNReal.ofReal (Real.exp (ρ * X.X (Real.toNNReal h) ω) *
          (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P) ≤
          ENNReal.ofReal (C * h) := by
  obtain ⟨C, hC, hRate⟩ :=
    avram_p2_original_all_positive_tilts_fourth_weighted_linear_smalltime_bound
      X ρ hρ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hRate] with h hb
  have hi : Integrable (fun ω => Real.exp
      (ρ * X.X (Real.toNNReal h) ω) *
      (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) P :=
    avram_p2_original_all_positive_tilts_fourth_weighted_integrable
      X (Real.toNNReal h) ρ hρ
  have hn : 0 ≤ᵐ[P] (fun ω => Real.exp
      (ρ * X.X (Real.toNNReal h) ω) *
      (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) := by
    filter_upwards [] with ω
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  exact ENNReal.ofReal_le_ofReal hb
