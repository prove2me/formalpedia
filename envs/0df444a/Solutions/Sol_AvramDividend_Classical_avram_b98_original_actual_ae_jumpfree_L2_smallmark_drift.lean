-- Prove2me | solution 1 for AvramDividend.Classical.avram_b98_original_actual_ae_jumpfree_L2_smallmark_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:20:50.207197+00:00
-- url     : https://prove2.me/submissions/c03c89b8-fb81-4725-859e-f99df1ddcd72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
import Theorems.Thm_AvramDividend_Classical_avram_b97_original_finiteactivity_ae_smallmark_limit_drift_from_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original a.e. jumpfree source increments have the exact limiting signed compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      s ω < u → u ≤ t ω →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ T : ℝ≥0, Integrable (fun ω => (Jsmall T ω) ^ 2) P) ∧
      (∀ᵐ ω ∂P,
        Jsmall (t ω) ω - Jsmall (s ω) ω =
          - ((t ω : ℝ) - (s ω : ℝ)) *
            (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) := by
  have hBand : ∀ᵐ ω ∂P, ∀ n : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
        - ((t ω : ℝ) - (s ω : ℝ)) *
          (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν) := by
    filter_upwards [hNoJump] with ω hNoJumpω
    intro n
    exact avram_b80_original_jumpfree_cell_smallband_compensator_increment
      X n (s ω) (t ω) (hOrder ω) ω hNoJumpω
  exact avram_b97_original_finiteactivity_ae_smallmark_limit_drift_from_band
    X hX hFinite s t
    (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)
    hBand
    (avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit X hFinite)
