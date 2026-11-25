-- Prove2me | solution 1 for DiscreteStability.StepBound.inner_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:38:50.589737+00:00
-- url     : https://prove2.me/submissions/a58cc267-40b9-4ab9-938c-66e614acff7e

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic
import Theorems.Thm_DiscreteStability_StepBound_psd

set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open DiscreteStability.StepBound
variable {P : E →L[ℝ] E} {lo hi : ℝ}
namespace DiscreteStability.StepBound
theorem _root_.solution (h : StepBound P lo hi) (u v : E) :
    ⟪P u, v⟫ ^ 2 ≤ ⟪P u, u⟫ * ⟪P v, v⟫ := by
  have hs : ⟪P v, u⟫ = ⟪P u, v⟫ := (h.symm v u).trans (real_inner_comm (P u) v)
  have key : ∀ t : ℝ, 0 ≤ ⟪P v, v⟫ * (t * t) + (2 * ⟪P u, v⟫) * t + ⟪P u, u⟫ := by
    intro t
    have h0 := h.psd (u + t • v)
    have e : ⟪P (u + t • v), u + t • v⟫
        = ⟪P v, v⟫ * (t * t) + (2 * ⟪P u, v⟫) * t + ⟪P u, u⟫ := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hs]
      ring
    rw [e] at h0
    exact h0
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]
end DiscreteStability.StepBound
