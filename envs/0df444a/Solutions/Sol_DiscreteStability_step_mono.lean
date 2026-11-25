-- Prove2me | solution 1 for DiscreteStability.step_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:00:19.7358+00:00
-- url     : https://prove2.me/submissions/edbb3fc7-b0ff-45c8-9dca-6f3d96841865

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
import Theorems.Thm_DiscreteStability_segment_ge

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
    f x ≤ f (x + P (g x)) := by
  simpa using segment_ge hP hL hS1 le_rfl hseg hgrad hlip 1 ⟨zero_le_one, le_rfl⟩
end DiscreteStability
