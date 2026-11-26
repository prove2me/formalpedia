-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.norm_sub_le_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:33.486823+00:00
-- url     : https://prove2.me/submissions/2e95cc14-0e38-4525-af29-2894123c8abe

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_deriv_le_of_bounded

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {f : ℂ → ℂ} {M ρ : ℝ} {c : ℂ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (ball c (2 * ρ)))
    (hb : ∀ w ∈ ball c (2 * ρ), ‖f w‖ ≤ M)
    {x y : ℂ} (hx : x ∈ ball c ρ) (hy : y ∈ ball c ρ) :
    ‖f x - f y‖ ≤ (2 * M / ρ) * ‖x - y‖ := by
  have hsub : ball c ρ ⊆ ball c (2 * ρ) := by
    intro v hv
    rw [Metric.mem_ball] at hv ⊢
    linarith
  have hder : ∀ v ∈ ball c ρ, HasFDerivWithinAt f
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f v)) (ball c ρ) v := by
    intro v hv
    exact (((hf.differentiableAt
      (isOpen_ball.mem_nhds (hsub hv))).hasDerivAt).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ v ∈ ball c ρ,
      ‖ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f v)‖ ≤ 2 * M / ρ := by
    intro v hv
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
    have hvb : dist v c < ρ := by rwa [Metric.mem_ball] at hv
    have hball : closedBall v (ρ / 2) ⊆ ball c (2 * ρ) := by
      intro w hw
      rw [Metric.mem_closedBall] at hw
      rw [Metric.mem_ball]
      calc dist w c ≤ dist w v + dist v c := dist_triangle _ _ _
        _ < 2 * ρ := by linarith
    have hcauchy := norm_deriv_le_of_bounded isOpen_ball hf
      (by linarith : (0 : ℝ) < ρ / 2) hball hb
    calc ‖deriv f v‖ ≤ M / (ρ / 2) := hcauchy
      _ = 2 * M / ρ := by field_simp
  exact (convex_ball c ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound hy hx
end ExponentialJuliaSetMisiurewicz
