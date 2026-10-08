-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.projOp_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T10:37:10.300533+00:00
-- url     : https://prove2.me/submissions/444142f4-74bb-4ad8-ad13-269ea4d92f12

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.projOp_apply_mem
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution (x : H) : projOp V x ∈ V := V.starProjection_apply_mem x
