-- Prove2me | solution 1 for DiscreteStability.StepBound.hi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:32:29.449069+00:00
-- url     : https://prove2.me/submissions/d410555d-27aa-4776-b109-21b14716d5ba

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic

set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open DiscreteStability.StepBound
variable {P : E →L[ℝ] E} {lo hi : ℝ}
namespace DiscreteStability.StepBound
theorem _root_.solution (h : StepBound P lo hi) : 0 ≤ hi := h.lo_nonneg.trans h.lo_le_hi
end DiscreteStability.StepBound
