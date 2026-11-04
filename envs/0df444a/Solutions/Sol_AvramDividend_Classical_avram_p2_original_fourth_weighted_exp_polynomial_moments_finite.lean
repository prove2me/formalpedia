-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_polynomial_moments_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:04:41.340732+00:00
-- url     : https://prove2.me/submissions/1d2827d5-31f8-420a-bfd4-e3cb4b4aba94

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every polynomial moment of the original fourth-weighted exponential
source law is finite, using exact nonnegative tilt integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
      ENNReal.ofReal ((Real.exp (X.X t ω)) ^ k) ∂P) < ⊤ := by
  have hi : Integrable (fun ω => Real.exp ((k : ℝ) * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4) P :=
    avram_p2_original_all_positive_tilts_fourth_weighted_integrable
      X t (k : ℝ) (by positivity)
  have hFinite :
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((k : ℝ) * X.X t ω) *
        (Real.exp (X.X t ω) - 1) ^ 4) ∂P) < ⊤ :=
    (lintegral_ofReal_le_lintegral_enorm _).trans_lt hi.hasFiniteIntegral
  have hEq :
      (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
        ENNReal.ofReal ((Real.exp (X.X t ω)) ^ k) ∂P) =
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((k : ℝ) * X.X t ω) *
        (Real.exp (X.X t ω) - 1) ^ 4) ∂P) := by
    congr 1
    funext ω
    rw [← Real.exp_nat_mul (X.X t ω) k,
      ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    exact mul_comm _ _
  exact hEq.le.trans_lt hFinite
