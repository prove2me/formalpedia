-- Prove2me | solution 1 for AvramDividend.Classical.avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:05:31.859202+00:00
-- url     : https://prove2.me/submissions/e1dfc74c-b075-4fa8-9c71-0949cd87b0f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a68_original_gaussian_and_physical_jump_measurable_pair_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a69_original_levy_drift_shifted_exponential_laplace_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a70_original_gaussian_physical_jump_independence_marginal_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a67_nonpositive_jump_exponential_bounded_integrable_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ (t : ℝ≥0) (ht : 0 < t) (θ : ℝ), 0 < θ →
      ∃ (H J : Ω → ℝ) (a b : ℝ),
        Measurable H ∧ Measurable J ∧
        (H =ᵐ[P] R t) ∧
        (J =ᵐ[P] fun ω =>
          ∑' u : ℝ≥0,
            if 0 < u ∧ u ≤ t then
              X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
            else 0) ∧
        IndepFun (fun ω => Real.exp (θ * H ω))
          (fun ω => Real.exp (θ * J ω)) P ∧
        Integrable (fun ω => Real.exp (θ * (H ω + J ω))) P ∧
        Integrable (fun ω => Real.exp (θ * J ω)) P ∧
        (∫ ω, Real.exp (θ * (H ω + J ω)) ∂P) = Real.exp a ∧
        (∫ ω, Real.exp (θ * J ω) ∂P) = Real.exp b ∧
        a - b = (t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t ht θ hθ
  obtain ⟨H, J, hHMeas, hJMeas, hHEq, hJEq, hDecomp⟩ :=
    avram_a68_original_gaussian_and_physical_jump_measurable_pair_20261114
      X hFinite R hR t
  let d : ℝ :=
    (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)
  let a : ℝ := (t : ℝ) * X.ψ θ - θ * d
  let b : ℝ := a - (t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)
  obtain ⟨hIndependent, hJumpLaplace⟩ :=
    avram_a70_original_gaussian_physical_jump_independence_marginal_20261114
      X hX hFinite hPositive hNu R hR
      t ht θ hθ H J hHMeas hJMeas hHEq hJEq hDecomp
  have hJumpNonpos : ∀ᵐ ω ∂P, J ω ≤ 0 := by
    filter_upwards [hJEq,
      avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
        X hFinite] with ω hJω hω
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    obtain ⟨S, hS, hSN⟩ := hω t
    have hTsum :
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then j u else 0) =
          (∑ u ∈ S, if u ≤ t then j u else 0) :=
      avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
        j t S hS t le_rfl
    rw [hJω]
    change (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then j u else 0) ≤ 0
    rw [hTsum]
    exact hSN t le_rfl
  have hJInt : Integrable (fun ω => Real.exp (θ * J ω)) P :=
    (avram_a67_nonpositive_jump_exponential_bounded_integrable_20261114
      J θ hJMeas (le_of_lt hθ) hJumpNonpos).1
  have hShiftLaw :=
    avram_a69_original_levy_drift_shifted_exponential_laplace_20261114
      X t θ d (le_of_lt hθ)
  have hPoint (ω : Ω) :
      Real.exp (θ * (H ω + J ω)) =
        Real.exp (θ * (X.X t ω - d)) := by
    rw [hDecomp ω]
  have hFun :
      (fun ω => Real.exp (θ * (H ω + J ω))) =
        (fun ω => Real.exp (θ * (X.X t ω - d))) :=
    funext hPoint
  have hProductInt :
      Integrable (fun ω => Real.exp (θ * (H ω + J ω))) P := by
    rw [hFun]
    exact hShiftLaw.1
  have hProductLaplace :
      (∫ ω, Real.exp (θ * (H ω + J ω)) ∂P) =
        Real.exp a := by
    rw [hFun]
    exact hShiftLaw.2
  refine ⟨H, J, a, b, hHMeas, hJMeas, hHEq, hJEq,
    hIndependent, hProductInt, hJInt, hProductLaplace, ?_, ?_⟩
  · exact hJumpLaplace
  · dsimp [b]
    ring
