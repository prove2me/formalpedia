-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.proj_mul_truncGen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:49:55.33092+00:00
-- url     : https://prove2.me/submissions/682c4784-cde2-478f-8249-885092b80984

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.proj_mul_truncGen
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_apply_mem
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_eq_self_of_mem
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution : projOp V * BookProof.BrstUnboundedLeakage.truncGen T V hV = BookProof.BrstUnboundedLeakage.truncGen T V hV := by

  ext x
  simp [BookProof.BrstUnboundedLeakage.truncGen, ContinuousLinearMap.mul_apply,
    projOp_eq_self_of_mem V (projOp_apply_mem V _)]
