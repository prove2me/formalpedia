-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_integrable_upto_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:35:45.561198+00:00
-- url     : https://prove2.me/submissions/dc2a9d24-bf8f-4d1a-a374-81dec46b37e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ht : t ≤ 1) :
    Integrable (fun ω => (t : ℝ) * X.drift - X.X t ω) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hInt1 :
      Integrable (fun ω : Ω => (1 : ℝ) * X.drift - X.X 1 ω) P := by
    convert (integrable_const X.drift).sub hX.2.1 using 1
    funext ω
    simp
  have hMeas : Measurable
      (fun ω : Ω => (t : ℝ) * X.drift - X.X t ω) :=
    measurable_const.sub ((X.adapted t).mono (𝓕.le _) le_rfl)
  have hb : ∀ᵐ ω ∂P,
      ‖(t : ℝ) * X.drift - X.X t ω‖ ≤
        (1 : ℝ) * X.drift - X.X 1 ω := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have h0 := hm (show (0 : ℝ≥0) ≤ t from bot_le)
    have h1 := hm ht
    have hr0 : 0 ≤ (t : ℝ) * X.drift - X.X t ω := by
      simpa [X.X_zero] using h0
    have hr1 :
        (t : ℝ) * X.drift - X.X t ω ≤
        (1 : ℝ) * X.drift - X.X 1 ω := h1
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  exact hInt1.mono' hMeas.aestronglyMeasurable hb