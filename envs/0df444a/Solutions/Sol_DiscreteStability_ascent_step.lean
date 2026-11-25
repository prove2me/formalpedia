-- Prove2me | solution 1 for DiscreteStability.ascent_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:57:16.656058+00:00
-- url     : https://prove2.me/submissions/596ec49d-c789-4093-a4ca-f770b136a45d

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
import Theorems.Thm_DiscreteStability_ascent

set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}
namespace DiscreteStability
theorem _root_.solution (hP : StepBound P lo hi) (hL : 0 ≤ L) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + (1 - L * hi / 2) * ⟪P (g x), g x⟫ ≤ f (x + P (g x)) := by
  have := ascent hP hL hseg hgrad hlip 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_smul, one_mul] at this
  convert this using 2
  ring
end DiscreteStability
