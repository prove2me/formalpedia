-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_truncated_residual_source_jump_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:16:50.852724+00:00
-- url     : https://prove2.me/submissions/f3dd5ab7-b3fb-46b5-b2ae-7425ec794933

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact same-path cutoff residual obtained from X.X, its own jump series,
and its own deterministic Levy measure, with no Gaussian source assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) t ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
      X.X t ω - (t : ℝ) * X.c -
        ((∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
            E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0) -
          (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) -
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω := by
  classical
  simp only [avram_p4_h_gaussian_intrinsic_truncated_residual,
    avram_p4_h_gaussian_intrinsic_small_band_compensated]
  rw [avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum X ω t n]
