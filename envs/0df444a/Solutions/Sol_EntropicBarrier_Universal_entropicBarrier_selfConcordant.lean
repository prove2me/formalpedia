-- Prove2me | solution 1 for EntropicBarrier.Universal.entropicBarrier_selfConcordant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T14:02:42.896223+00:00
-- url     : https://prove2.me/submissions/1fb4386a-73e4-459b-bb40-103634c7f145

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Theorems.Thm_EntropicBarrier_Universal_entropicBarrier_line_derivatives
import Theorems.Thm_EntropicBarrier_Universal_logPartition_moment_inequality

open scoped RealInnerProductSpace
open MeasureTheory

open EntropicBarrier.Universal in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    ConvexOptimization.IsSelfConcordantOn (interior K) (entropicBarrier K) := by
  obtain ⟨hconv, hsmooth, hline⟩ := entropicBarrier_line_derivatives K hK
  refine ⟨hconv, hsmooth, ?_⟩
  intro x hx v
  obtain ⟨θ, h, -, -, h2, h3⟩ := hline x hx v
  rw [h2, h3]
  have hp := logPartition_moment_inequality K hK θ h
  have hm := logPartition_moment_inequality K hK θ (-h)
  have e3 : (fun y => ⟪y - meanMap K θ, -h⟫ ^ 3) =
      fun y => -(⟪y - meanMap K θ, h⟫ ^ 3) := by
    funext y; rw [inner_neg_right]; ring
  have e2 : (fun y => ⟪y - meanMap K θ, -h⟫ ^ 2) =
      fun y => ⟪y - meanMap K θ, h⟫ ^ 2 := by
    funext y; rw [inner_neg_right]; ring
  rw [e3, e2, integral_neg] at hm
  rw [abs_neg, abs_le]
  constructor <;> linarith
