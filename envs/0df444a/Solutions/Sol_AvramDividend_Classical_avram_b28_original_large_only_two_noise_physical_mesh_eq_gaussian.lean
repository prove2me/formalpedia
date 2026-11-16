-- Prove2me | solution 1 for AvramDividend.Classical.avram_b28_original_large_only_two_noise_physical_mesh_eq_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:55:46.844949+00:00
-- url     : https://prove2.me/submissions/e65d6606-394c-4d42-a4cc-f26d7767d2b6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_intrinsic_gaussian_unique_physical_mesh
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_no_small_negative_jump_limit_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (R B Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hBsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (B t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω)))
    (σ : Ω → ℝ≥0) (S : Finset ℕ)
    (a b : ℕ → ℝ≥0) (WG WJ : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) +
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) =
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
        (B (b i) ω - B (a i) ω)) := by
  have hGauss :=
    avram_b28_original_intrinsic_gaussian_unique_physical_mesh
      X R B hRsource hBsource σ S a b WG
  have hJzero :=
    avram_b28_original_no_small_negative_jump_limit_zero
      X hν hLarge Jsmall hJsource
  filter_upwards [hGauss, hJzero] with ω hG hJ
  have hZero :
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hJ (b i), hJ (a i)]
  rw [hZero, add_zero]
  exact hG
