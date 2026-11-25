-- Prove2me | solution 1 for DiscreteStability.step_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:03:59.4088+00:00
-- url     : https://prove2.me/submissions/a67238aa-4f6c-47a9-a902-84c6ca89bc87

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
import Theorems.Thm_DiscreteStability_step_weighted

set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}
namespace DiscreteStability
theorem _root_.solution (hP : StepBound P lo hi) (hL : 0 ≤ L) {η : ℝ} (hS2 : L * hi ≤ 2 - η)
    (hη : 0 ≤ η) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + η / 2 * lo * ‖g x‖ ^ 2 ≤ f (x + P (g x)) := by
  have h := step_weighted hP hL (by linarith) hseg hgrad hlip
  have h1 : η / 2 * lo * ‖g x‖ ^ 2 ≤ lo * (2 - L * hi) / 2 * ‖g x‖ ^ 2 := by
    have := mul_nonneg hP.lo_nonneg (sq_nonneg ‖g x‖)
    nlinarith
  linarith
end DiscreteStability
