-- Prove2me | solution 1 for DiscreteStability.StepBound.norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:53:38.719189+00:00
-- url     : https://prove2.me/submissions/41733f0d-b15a-4f60-beab-5b53a8a7a69b

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic
import Theorems.Thm_DiscreteStability_StepBound_hi_nonneg
import Theorems.Thm_DiscreteStability_StepBound_norm_sq_le

set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open DiscreteStability.StepBound
variable {P : E →L[ℝ] E} {lo hi : ℝ}
namespace DiscreteStability.StepBound
theorem _root_.solution (h : StepBound P lo hi) (u : E) : ‖P u‖ ≤ hi * ‖u‖ := by
  have h1 := h.norm_sq_le u
  have h2 : ⟪P u, u⟫ ≤ ‖P u‖ * ‖u‖ := real_inner_le_norm _ _
  have h3 := mul_le_mul_of_nonneg_left h2 h.hi_nonneg
  rcases (norm_nonneg (P u)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg h.hi_nonneg (norm_nonneg _)
  · have : ‖P u‖ * ‖P u‖ ≤ (hi * ‖u‖) * ‖P u‖ := by nlinarith [h1, h3]
    exact le_of_mul_le_mul_right this hpos
end DiscreteStability.StepBound
