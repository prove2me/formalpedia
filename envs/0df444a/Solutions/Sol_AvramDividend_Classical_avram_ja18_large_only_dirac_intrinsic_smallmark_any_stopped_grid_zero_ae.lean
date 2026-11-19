-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_large_only_dirac_intrinsic_smallmark_any_stopped_grid_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:19:01.38292+00:00
-- url     : https://prove2.me/submissions/606dc1dc-fba7-4a22-86a6-be7c93d38e87

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_no_small_negative_jump_limit_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact finite stopped small-band meshes vanish in a source with only large negative marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = Measure.dirac (-2 : ℝ))
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
       X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (WJ : ℕ → Ω → ℝ) (σ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, (∑ i ∈ S,
      (if σ ω ≤ a i then 0 else WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) = 0 := by
  have hnu_small : X.ν (Ioc (-1 : ℝ) 0) = 0 := by
    rw [hν]
    norm_num [Measure.dirac_apply, Set.mem_Ioc]
  have hzero : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Jsmall u ω = 0 :=
    avram_b28_original_no_small_negative_jump_limit_zero
      X hnu_small hLarge Jsmall hJsource
  filter_upwards [hzero] with ω hω
  simp [hω]
