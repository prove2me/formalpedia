-- Prove2me | solution 1 for DiscreteStability.StepBound.psd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:32:40.606024+00:00
-- url     : https://prove2.me/submissions/d971a649-0314-49bc-b228-4e95fea28909

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
theorem _root_.solution (h : StepBound P lo hi) (u : E) : 0 ≤ ⟪P u, u⟫ :=
  le_trans (mul_nonneg h.lo_nonneg (sq_nonneg _)) (h.lower u)
end DiscreteStability.StepBound
