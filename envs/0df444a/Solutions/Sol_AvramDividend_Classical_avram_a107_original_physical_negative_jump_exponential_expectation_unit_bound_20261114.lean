-- Prove2me | solution 1 for AvramDividend.Classical.avram_a107_original_physical_negative_jump_exponential_expectation_unit_bound_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:01:33.082493+00:00
-- url     : https://prove2.me/submissions/be4f4862-53f7-41d6-a40f-db030e790428

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    (∫ ω, Real.exp (θ * J ω) ∂P) ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hInt, hBound⟩ :=
    avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite T θ hθ J hJMeas hJEq
  have hUnit : Integrable (fun _ : Ω => (1 : ℝ)) P :=
    integrable_const _
  have hLE : (fun ω => Real.exp (θ * J ω)) ≤ᵐ[P]
      (fun _ : Ω => (1 : ℝ)) := by
    filter_upwards [hBound] with ω hω
    exact hω.2
  have hIntegral := integral_mono_ae hInt hUnit hLE
  simpa [integral_const, Measure.real, measure_univ, smul_eq_mul] using hIntegral
