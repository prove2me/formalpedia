-- Prove2me | solution 3 for AvramDividend.Classical.avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:43:19.613139+00:00
-- url     : https://prove2.me/submissions/1ae4be60-9022-426e-8d54-82c5ff0e3cd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a68_original_gaussian_and_physical_jump_measurable_pair_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a69_original_levy_drift_shifted_exponential_laplace_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a70_original_gaussian_physical_jump_independence_marginal_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
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
  intro t ht θ hθ
  obtain ⟨H, J, hHM, hJM, hHEq, hJEq, hDecomp⟩ :=
    avram_a68_original_gaussian_and_physical_jump_measurable_pair_20261114
      X hFinite R hR t
  obtain ⟨hInd, hJump⟩ :=
    avram_a70_original_gaussian_physical_jump_independence_marginal_20261114
      X hX hFinite hPositive hNu R hR t ht θ hθ
      H J hHM hJM hHEq hJEq hDecomp
  let d : ℝ := (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)
  let a : ℝ := (t : ℝ) * X.ψ θ - θ * d
  let b : ℝ := a - (t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)
  have hSource :=
    avram_a69_original_levy_drift_shifted_exponential_laplace_20261114
      X t θ d (le_of_lt hθ)
  have hSame :
      (fun ω => Real.exp (θ * (H ω + J ω))) =
        (fun ω => Real.exp (θ * (X.X t ω - d))) := by
    funext ω
    rw [hDecomp ω]
  have hProductInt : Integrable
      (fun ω => Real.exp (θ * (H ω + J ω))) P := by
    rw [hSame]
    exact hSource.1
  have hProductMean :
      (∫ ω, Real.exp (θ * (H ω + J ω)) ∂P) = Real.exp a := by
    rw [hSame]
    exact hSource.2
  have hJumpInt :=
    (avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ (le_of_lt hθ) J hJM hJEq).1
  refine ⟨H, J, a, b, hHM, hJM, hHEq, hJEq, hInd,
    hProductInt, hJumpInt, hProductMean, ?_, ?_⟩
  · simpa only [b, a, d] using hJump
  · dsimp [b]
    ring
