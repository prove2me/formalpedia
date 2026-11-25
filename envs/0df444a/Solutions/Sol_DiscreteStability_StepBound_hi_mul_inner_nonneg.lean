-- Prove2me | solution 1 for DiscreteStability.StepBound.hi_mul_inner_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:05.571428+00:00
-- url     : https://prove2.me/submissions/0b3c8d02-7a03-4fcf-8560-39ff08fe7dc0

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic
import Theorems.Thm_DiscreteStability_StepBound_hi_nonneg
import Theorems.Thm_DiscreteStability_StepBound_psd

set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open DiscreteStability.StepBound
variable {P : E →L[ℝ] E} {lo hi : ℝ}
namespace DiscreteStability.StepBound
theorem _root_.solution (h : StepBound P lo hi) (u : E) : 0 ≤ hi * ⟪P u, u⟫ :=
  mul_nonneg h.hi_nonneg (h.psd u)
end DiscreteStability.StepBound
