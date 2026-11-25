-- Prove2me | solution 1 for DiscreteStability.StepBound.norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:48:33.205319+00:00
-- url     : https://prove2.me/submissions/4edecc9f-ffa1-44b5-a51f-c3741bfe3ca9

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic
import Theorems.Thm_DiscreteStability_StepBound_psd
import Theorems.Thm_DiscreteStability_StepBound_inner_sq_le
import Theorems.Thm_DiscreteStability_StepBound_hi_mul_inner_nonneg

set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open DiscreteStability.StepBound
variable {P : E →L[ℝ] E} {lo hi : ℝ}
namespace DiscreteStability.StepBound
theorem _root_.solution (h : StepBound P lo hi) (u : E) : ‖P u‖ ^ 2 ≤ hi * ⟪P u, u⟫ := by
  have h1 := h.inner_sq_le u (P u)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 := h.upper (P u)
  have h3 := h.psd u
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  rcases (sq_nonneg ‖P u‖).eq_or_lt with h0 | hpos
  · rw [← h0]; exact h.hi_mul_inner_nonneg u
  · have : ‖P u‖ ^ 2 * ‖P u‖ ^ 2 ≤ (hi * ⟪P u, u⟫) * ‖P u‖ ^ 2 := by nlinarith [h1, h4]
    exact le_of_mul_le_mul_right this hpos
end DiscreteStability.StepBound
