-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_weighted_exp_real_moment_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:56:34.689653+00:00
-- url     : https://prove2.me/submissions/0f2bb6d0-9287-4044-8433-942cfa8bc60c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_pushforward_moment_formula
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The kth ENNReal moment of the actual original finite weighted
exponential image is the ofReal of its true tilted real expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X t ω)))) =
    ENNReal.ofReal (∫ ω, Real.exp ((k : ℝ) * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4 ∂P) := by
  have hi : Integrable (fun ω => Real.exp ((k : ℝ) * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4) P :=
    avram_p2_original_all_positive_tilts_fourth_weighted_integrable
      X t (k : ℝ) (by positivity)
  have hn : 0 ≤ᵐ[P] (fun ω => Real.exp ((k : ℝ) * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4) := by
    filter_upwards [] with ω
    positivity
  rw [avram_p2_original_fourth_weighted_exp_pushforward_moment_formula X t k]
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_congr_ae
  filter_upwards [] with ω
  rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  rw [Real.exp_nat_mul]
  ac_rfl
