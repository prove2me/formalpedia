-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_ae_intrinsic_two_limits_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:22:02.657215+00:00
-- url     : https://prove2.me/submissions/88897c09-f6e5-4895-9ac3-271aa5972d4e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_ae_intrinsic_two_limits_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) :
    (∀ u : ℝ≥0, Integrable (R u) P) ∧
    (∀ u : ℝ≥0, Integrable (Jsmall u) P)  := by
  exact avram_b24_original_finiteactivity_ae_intrinsic_two_limits_integrable
    X hX hFinite R Jsmall hRsource hJsource
