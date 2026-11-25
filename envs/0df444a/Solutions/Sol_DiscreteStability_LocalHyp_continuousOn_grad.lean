-- Prove2me | solution 1 for DiscreteStability.LocalHyp.continuousOn_grad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:50.178132+00:00
-- url     : https://prove2.me/submissions/2af478cc-b3e1-4a57-aaec-cfc4bb26f8b4

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
import Theorems.Thm_DiscreteStability_continuousOn_of_lip


set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
namespace DiscreteStability
namespace LocalHyp
theorem _root_.solution (hH : LocalHyp f g xbar r₀ L) :
    ContinuousOn g (closedBall xbar r₀) :=
  continuousOn_of_lip hH.L_nonneg hH.lip
end LocalHyp
end DiscreteStability
