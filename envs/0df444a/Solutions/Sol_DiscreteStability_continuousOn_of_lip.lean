-- Prove2me | solution 1 for DiscreteStability.continuousOn_of_lip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:32:43.213135+00:00
-- url     : https://prove2.me/submissions/4c1e65df-1c7c-4501-bf11-66f3f057a624

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic

set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
omit [InnerProductSpace ℝ E]
namespace DiscreteStability
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] {g : E → F} {S : Set E} {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) : ContinuousOn g S := by
  intro z hz
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (L + 1), by positivity, fun {y} hy hyz => ?_⟩
  rw [dist_eq_norm] at hyz ⊢
  calc ‖g y - g z‖ ≤ L * ‖y - z‖ := h y hy z hz
    _ ≤ (L + 1) * ‖y - z‖ := by nlinarith [norm_nonneg (y - z)]
    _ < (L + 1) * (ε / (L + 1)) := by gcongr
    _ = ε := by field_simp
end DiscreteStability
