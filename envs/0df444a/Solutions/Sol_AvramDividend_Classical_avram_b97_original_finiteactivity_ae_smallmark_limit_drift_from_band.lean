-- Prove2me | solution 1 for AvramDividend.Classical.avram_b97_original_finiteactivity_ae_smallmark_limit_drift_from_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:16:59.910812+00:00
-- url     : https://prove2.me/submissions/72da45a0-f085-435c-80fa-bcbcf1d8d7b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_smallband_limit_square_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine a.e. original small-band limit produces exact jumpfree compensator drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : Ω → ℝ≥0) (c : ℝ)
    (hBand : ∀ᵐ ω ∂P, ∀ n : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
        - ((t ω : ℝ) - (s ω : ℝ)) *
          (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
    (hMoment : Tendsto (fun n : ℕ =>
      ∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)
      atTop (𝓝 c)) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ T : ℝ≥0, Integrable (fun ω => (Jsmall T ω) ^ 2) P) ∧
      (∀ᵐ ω ∂P,
        Jsmall (t ω) ω - Jsmall (s ω) ω =
          - ((t ω : ℝ) - (s ω : ℝ)) * c) := by
  obtain ⟨Jsmall, hLim, hL2⟩ :=
    avram_ja19_original_finite_activity_smallband_limit_square_L1 X hX hFinite
  refine ⟨Jsmall, hL2, ?_⟩
  filter_upwards [hLim, hBand] with ω hLimω hBandω
  have hD := (hLimω (t ω)).sub (hLimω (s ω))
  have hEq :
      (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω) =
      (fun n : ℕ => - ((t ω : ℝ) - (s ω : ℝ)) *
        (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) := by
    funext n
    exact hBandω n
  rw [hEq] at hD
  have hM : Tendsto (fun n : ℕ =>
      - ((t ω : ℝ) - (s ω : ℝ)) *
        (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 (- ((t ω : ℝ) - (s ω : ℝ)) * c)) :=
    tendsto_const_nhds.mul hMoment
  exact tendsto_nhds_unique hD hM
