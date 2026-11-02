-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:39:26.66145+00:00
-- url     : https://prove2.me/submissions/a1e95362-53dc-4929-ab0d-9f9921b2d992

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ht : t ≤ 1) (M : ℝ) :
    Integrable
      (fun ω => if M < (t : ℝ) * X.drift - X.X t ω
        then (t : ℝ) * X.drift - X.X t ω else 0) P := by
  let R : Ω → ℝ := fun ω => (t : ℝ) * X.drift - X.X t ω
  have hRI : Integrable R P :=
    avram_wave5_04c_actual_bv_residual_integrable_upto_one X hX hBV t ht
  have hRM : Measurable R :=
    measurable_const.sub ((X.adapted t).mono (𝓕.le _) le_rfl)
  have hF : Measurable (fun r : ℝ => if M < r then r else 0) := by
    have hs : MeasurableSet {r : ℝ | M < r} := measurableSet_Ioi
    exact Measurable.ite hs measurable_id measurable_const
  have hBound : ∀ᵐ ω ∂P,
      ‖(if M < R ω then R ω else 0)‖ ≤ R ω := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have hr0 : 0 ≤ R ω := by
      simpa [R, X.X_zero] using hm (show (0 : ℝ≥0) ≤ t from bot_le)
    split_ifs with h
    · simp only [Real.norm_eq_abs, abs_of_nonneg hr0, le_refl]
    · simp only [norm_zero]
      exact hr0
  have hMeas := hF.comp hRM
  exact hRI.mono' hMeas.aestronglyMeasurable hBound