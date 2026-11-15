-- Prove2me | solution 1 for AvramDividend.Classical.avram_a70_original_gaussian_physical_jump_independence_marginal_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:07:26.234119+00:00
-- url     : https://prove2.me/submissions/5e7fc9f7-26d7-4199-9457-dbe0cd3d6bbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a71_original_gaussian_physical_negative_jump_independence_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a72_original_physical_negative_jump_total_exact_laplace_20261114
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
        atTop (𝓝 (R t ω)))
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (H J : Ω → ℝ)
    (hHMeas : Measurable H) (hJMeas : Measurable J)
    (hHEq : H =ᵐ[P] R t)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hDecomp : ∀ ω, H ω + J ω =
      X.X t ω -
        (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) :
    IndepFun (fun ω => Real.exp (θ * H ω))
      (fun ω => Real.exp (θ * J ω)) P ∧
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) * X.ψ θ -
        θ * ((t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) -
        (t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)) := by
  constructor
  · exact
      avram_a71_original_gaussian_physical_negative_jump_independence_20261114
        X hX hFinite hPositive hNu R hR t ht θ hθ
        H J hHMeas hJMeas hHEq hJEq hDecomp
  · exact
      avram_a72_original_physical_negative_jump_total_exact_laplace_20261114
        X hX hFinite hPositive hNu R hR t ht θ hθ
        H J hHMeas hJMeas hHEq hJEq hDecomp
