-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_tail_expected_monotone_upto_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:45:41.466678+00:00
-- url     : https://prove2.me/submissions/e9342dfd-9feb-469f-a7b3-b7f78c3fd825

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
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
    (∫ ω, if M < (t : ℝ) * X.drift - X.X t ω
      then (t : ℝ) * X.drift - X.X t ω else 0 ∂P) ≤
    (∫ ω, if M < (1 : ℝ) * X.drift - X.X 1 ω
      then (1 : ℝ) * X.drift - X.X 1 ω else 0 ∂P) := by
  let R : ℝ≥0 → Ω → ℝ :=
    fun s ω => (s : ℝ) * X.drift - X.X s ω
  let F : ℝ → ℝ := fun z => if M < z then z else 0
  have hIntt : Integrable (fun ω => F (R t ω)) P := by
    simpa only [R, F] using
      avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
        X hX hBV t ht M
  have hInt1 : Integrable (fun ω => F (R 1 ω)) P := by
    simpa only [R, F] using
      avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
        X hX hBV 1 le_rfl M
  have hpoint : ∀ᵐ ω ∂P, F (R t ω) ≤ F (R 1 ω) := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have hR0 : 0 ≤ R 1 ω := by
      simpa [R, X.X_zero] using
        hm (show (0 : ℝ≥0) ≤ 1 from bot_le)
    have hRle : R t ω ≤ R 1 ω := hm ht
    by_cases ha : M < R t ω
    · have hb : M < R 1 ω := lt_of_lt_of_le ha hRle
      simp only [F, if_pos ha, if_pos hb]
      exact hRle
    · by_cases hb : M < R 1 ω
      · simp only [F, if_neg ha, if_pos hb]
        exact hR0
      · simp [F, ha, hb]
  change (∫ ω, F (R t ω) ∂P) ≤ ∫ ω, F (R 1 ω) ∂P
  exact integral_mono_ae hIntt hInt1 hpoint