-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_finiteactivity_gaussian_intrinsic_centered_and_zero_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:47:28.525681+00:00
-- url     : https://prove2.me/submissions/ab2ba5dd-9b44-4793-b3c4-a0adf90104b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_any_activity_intrinsic_gaussian_source_zero_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    (∀ t : ℝ≥0, Integrable (R t) P ∧
      (∫ ω, R t ω ∂P) = 0) ∧
    (∀ᵐ ω ∂P, R 0 ω = 0) := by
  constructor
  · exact avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
      X hX hFinite R hRsource
  · exact avram_f6_original_any_activity_intrinsic_gaussian_source_zero_origin
      X R hRsource
