-- Prove2me | solution 1 for DiscreteStability.step_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:00:16.376522+00:00
-- url     : https://prove2.me/submissions/193e6ed6-d8a5-4335-9e02-488c8f74266d

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
import Theorems.Thm_DiscreteStability_ascent_step

set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}
namespace DiscreteStability
theorem _root_.solution (hP : StepBound P lo hi) (hL : 0 ≤ L) (hS1 : L * hi ≤ 2) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + lo * (2 - L * hi) / 2 * ‖g x‖ ^ 2 ≤ f (x + P (g x)) := by
  have h := ascent_step hP hL hseg hgrad hlip
  have hc : 0 ≤ 1 - L * hi / 2 := by linarith
  have := mul_le_mul_of_nonneg_left (hP.lower (g x)) hc
  nlinarith [this, h]
end DiscreteStability
