-- Prove2me | solution 1 for DiscreteStability.LocalHyp.continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:20.51974+00:00
-- url     : https://prove2.me/submissions/150e0d9f-f8cd-4f60-aa00-48ca9e721fa6

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability

set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
namespace DiscreteStability
namespace LocalHyp
theorem _root_.solution (hH : LocalHyp f g xbar r₀ L) : ContinuousOn f (closedBall xbar r₀) :=
  fun z hz => (hH.grad z hz).continuousAt.continuousWithinAt
end LocalHyp
end DiscreteStability
