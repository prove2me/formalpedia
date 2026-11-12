-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18l_intrinsic_residual_limit_zero_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:23:21.494897+00:00
-- url     : https://prove2.me/submissions/7576c06b-fc80-4cb6-ba6d-e5fb7464434b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every finite physical cutoff is zero at the original time origin;
its pointwise limit must be zero there as well. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, R 0 ω = 0 := by
  filter_upwards [hRsource] with ω hω
  have hZero :
      (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k 0 ω) =
        (fun _ : ℕ => (0 : ℝ)) := by
    funext k
    exact avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin X k ω
  have hh := hω 0
  rw [hZero] at hh
  exact (tendsto_nhds_unique tendsto_const_nhds hh).symm
