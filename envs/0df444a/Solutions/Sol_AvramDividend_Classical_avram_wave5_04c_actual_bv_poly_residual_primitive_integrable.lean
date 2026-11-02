-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_poly_residual_primitive_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T16:13:21.464003+00:00
-- url     : https://prove2.me/submissions/cb151fca-9280-4407-8f1f-cf67552ea7df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_nonnegative_random_poly_primitive_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! Actual original BV source polynomial jump residual primitive is
Bochner integrable at every nonnegative Lévy time, with no extra moments. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0)
    (t : ℝ≥0) :
    Integrable (fun ω => (∫ r in (0 : ℝ)..
      ((t : ℝ) * X.drift - X.X t ω),
      Polynomial.eval (Real.exp (-r)) p)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R : Ω → ℝ := fun ω => (t : ℝ) * X.drift - X.X t ω
  have hMeas : Measurable R :=
    measurable_const.sub ((X.adapted t).mono (𝓕.le _) le_rfl)
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have h0 := hm (show (0 : ℝ≥0) ≤ t from bot_le)
    simpa [R, X.X_zero] using h0
  exact avram_wave5_04c_nonnegative_random_poly_primitive_integrable
    R hMeas hNonneg p hp
