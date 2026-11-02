-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:41:30.339661+00:00
-- url     : https://prove2.me/submissions/45452899-941e-4799-b9ba-c1a58a9626de

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (h : ℝ≥0) (hhpos : 0 < h) (hhhalf : h ≤ (1 / 2 : ℝ≥0)) :
    (h : ℝ)⁻¹ * (∫ ω, (h : ℝ) * X.drift - X.X h ω ∂P)
      ≤ 2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) := by
  let R : ℝ≥0 → Ω → ℝ := fun t ω => (t : ℝ) * X.drift - X.X t ω
  have hnonneg (t : ℝ≥0) : ∀ᵐ ω ∂P, 0 ≤ R t ω := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    simpa [R, X.X_zero] using
      hm (show (0 : ℝ≥0) ≤ t from bot_le)
  have htail_eq (t : ℝ≥0) :
      (∫ ω, if 0 < R t ω then R t ω else 0 ∂P) =
      ∫ ω, R t ω ∂P := by
    apply integral_congr_ae
    filter_upwards [hnonneg t] with ω hr
    by_cases hc : 0 < R t ω
    · simp [hc]
    · have hz : R t ω = 0 := le_antisymm (le_of_not_gt hc) hr
      simp [hz]
  have ht := avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
    X hX hBV h hhpos hhhalf 0
  change (h : ℝ)⁻¹ * (∫ ω, if 0 < R h ω then R h ω else 0 ∂P) ≤
    2 * (∫ ω, if 0 < R 1 ω then R 1 ω else 0 ∂P) at ht
  rw [htail_eq h, htail_eq 1] at ht
  change (h : ℝ)⁻¹ * (∫ ω, R h ω ∂P) ≤ 2 * (∫ ω, R 1 ω ∂P)
  exact ht
