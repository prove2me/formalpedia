-- Prove2me | solution 1 for AvramDividend.Classical.avram_b63_original_jumpfree_clock_intrinsic_gaussian_drift_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:52:14.459495+00:00
-- url     : https://prove2.me/submissions/dfbca5ad-4831-400a-85f2-b881be99f36a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b62_original_jumpfree_random_clock_intrinsic_gaussian_drift_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original jump-free random-time Gaussian drift equality almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (d : ℝ)
    (hSmall : ∀ ω, Jsmall (t ω) ω - Jsmall (s ω) ω =
      d * ((t ω : ℝ) - (s ω : ℝ)))
    (hLarge : ∀ ω,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s ω) ω) :
    ∀ᵐ ω ∂P,
      X.X (t ω) ω - X.X (s ω) ω -
        ((t ω : ℝ) - (s ω : ℝ)) * X.c =
      (R (t ω) ω - R (s ω) ω) +
        d * ((t ω : ℝ) - (s ω : ℝ)) := by 
  obtain ⟨M, hPhysical, hMeq⟩ :=
    avram_b62_original_jumpfree_random_clock_intrinsic_gaussian_drift_exact
      X R Jsmall hRsource hJsource s t d hSmall hLarge
  filter_upwards [hMeq] with ω hEq
  calc
    X.X (t ω) ω - X.X (s ω) ω -
        ((t ω : ℝ) - (s ω : ℝ)) * X.c =
      (M (t ω) ω - M (s ω) ω) +
        d * ((t ω : ℝ) - (s ω : ℝ)) := hPhysical ω
    _ = _ := by rw [hEq (t ω), hEq (s ω)]
