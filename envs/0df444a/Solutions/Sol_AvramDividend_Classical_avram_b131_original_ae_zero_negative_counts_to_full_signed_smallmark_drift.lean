-- Prove2me | solution 1 for AvramDividend.Classical.avram_b131_original_ae_zero_negative_counts_to_full_signed_smallmark_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:36:40.038738+00:00
-- url     : https://prove2.me/submissions/b0370c5c-1ee0-4fc0-a5d8-a5406f74d0b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b110_original_negative_count_zero_forbids_actual_band_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_b130_original_negative_bandfree_cell_exact_compensation_drift
import Theorems.Thm_AvramDividend_Classical_avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All original negative Poisson band counts zero at the true random clocks imply exact full compensated smallmark drift on the same conull event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun n : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hZero : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s ω) (t ω) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) :
    ∀ᵐ ω ∂P, Jsmall (t ω) ω - Jsmall (s ω) ω =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        ((t ω : ℝ) - (s ω : ℝ)) := by
  have hCut : ∀ᵐ ω ∂P, ∀ n : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) := by
    filter_upwards [hZero] with ω hω
    intro n
    have hNoBand :=
      avram_b110_original_negative_count_zero_forbids_actual_band_source_jump
        X ω (s ω) (t ω) (hOrder ω) n (hω n)
    have h :=
      avram_b130_original_negative_bandfree_cell_exact_compensation_drift
        X n (s ω) (t ω) (hOrder ω) ω hNoBand
    rw [h]
    ring
  exact avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
    X hFinite Jsmall hJlim s t hCut
