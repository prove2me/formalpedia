-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.flow_truncGen_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:49:57.490805+00:00
-- url     : https://prove2.me/submissions/3e51a4fd-8171-435b-a31b-d2dd4c718306

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.flow_truncGen_mem
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_apply_mem
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_eq_self_of_mem
import Theorems.Thm_BookProof_BrstUnboundedLeakage_proj_mul_truncGen
import Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_mem_of_proj
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) {x : H} (hx : x ∈ V) : flow (truncGen T V hV) t x ∈ V := by

  have hx' : projOp V x = x := projOp_eq_self_of_mem V hx
  have h := flow_mem_of_proj (proj_mul_truncGen T V hV) t hx'
  rw [← h]
  exact projOp_apply_mem V _
