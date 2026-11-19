-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_largeonly_intrinsic_gaussian_residual_all_cutoffs_equal_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:31:12.842221+00:00
-- url     : https://prove2.me/submissions/bf6c3966-b5f4-4521-8da9-c6cff0d24cbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_omitted_negative_tail_equals_compensated_smallband_difference
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_no_small_negative_jump_limit_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The source's Gaussian cutoffs are all exactly equal when no small negative marks exist. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνsmall : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω = R t ω := by
  have hTail :=
    avram_ja18_original_omitted_negative_tail_equals_compensated_smallband_difference
      X R Jsmall hR hJ
  have hZero :=
    avram_b28_original_no_small_negative_jump_limit_zero
      X hνsmall hLarge Jsmall hJ
  filter_upwards [hTail, hZero, hLarge] with ω hω hsmall hlarge
  intro n t
  have hn :=
    avram_b27_original_no_small_band_marks_compensator_zero
      X hνsmall ω hlarge n t
  have hh := hω n t
  rw [hsmall t, hn] at hh
  linarith
