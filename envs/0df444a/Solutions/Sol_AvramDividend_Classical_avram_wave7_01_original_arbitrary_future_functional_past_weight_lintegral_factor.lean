-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:40:45.42347+00:00
-- url     : https://prove2.me/submissions/30764c82-e663-4934-a47c-0db28717e8d5

import Mathlib.Probability.Independence.Integration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original past factors from any measurable shifted-future reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (Fpath : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable Fpath) :
    (∫⁻ ω, H ω * Fpath (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) ∂P) =
    (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, Fpath (fun t : ℝ≥0 =>
        X.X (s + t) ω - X.X s ω) ∂P) := by
  have hPast : Measurable H :=
    hH.mono (𝓕.le s) le_rfl
  have hFuture : Measurable
      (fun ω : Ω => Fpath (fun t : ℝ≥0 =>
        X.X (s + t) ω - X.X s ω)) :=
    hF.comp (avram_wave7_01_original_shifted_future_path_coordinate_product_measurable X s)
  have hIndep : IndepFun H
      (fun ω : Ω => Fpath (fun t : ℝ≥0 =>
        X.X (s + t) ω - X.X s ω)) P :=
    actual_levy_past_indep_measurable_future_jump_family_ws01b
      X s H hH Fpath hF
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    hPast hFuture hIndep
