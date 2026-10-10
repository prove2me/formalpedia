-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.multOp_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:37:48.960989+00:00
-- url     : https://prove2.me/submissions/53a4add8-1760-4715-9f6d-65436e2f2e4d

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.multOp_comm
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (φ ψ : α → ℂ) (hφ : MemLp φ ⊤ μ) (hψ : MemLp ψ ⊤ μ) :
    (multOp φ hφ).comp (multOp ψ hψ) = (multOp ψ hψ).comp (multOp φ hφ) := by

  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [multOp_coeFn φ hφ (multOp ψ hψ f), multOp_coeFn ψ hψ f,
    multOp_coeFn ψ hψ (multOp φ hφ f), multOp_coeFn φ hφ f] with x h1 h2 h3 h4
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, h1, h2, h3, h4]
  ring
