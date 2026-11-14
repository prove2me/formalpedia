-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_allpath_gaussian_cutoff_rightcont_zero_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:52:46.107027+00:00
-- url     : https://prove2.me/submissions/30791f5a-5630-4e7a-8fdf-3e2518217293

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_smallband_cutoff_rightcont_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja18w_original_largejump_sum_rightcont
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original finite Gaussian residual cutoff is right-continuous on every path and starts at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (n : ℕ) (ω : Ω),
      (∀ t : ℝ≥0, ContinuousWithinAt
        (fun s : ℝ≥0 =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω)
        (Ici t) t) ∧
      avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω = 0 := by
  intro n ω
  refine ⟨?_, avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin X n ω⟩
  intro t
  have hX := X.rightCont ω t
  have hc : ContinuousWithinAt (fun u : ℝ≥0 => (u : ℝ) * X.c) (Ici t) t := by
    fun_prop
  have hSmall :=
    (avram_ja18g_original_smallband_cutoff_rightcont_zero X n ω).1 t
  have hLarge := avram_ja18w_original_largejump_sum_rightcont X ω t
  change ContinuousWithinAt (fun u : ℝ≥0 =>
      X.X u ω - (u : ℝ) * X.c -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) (Ici t) t
  exact ((hX.sub hc).sub hSmall).sub hLarge
