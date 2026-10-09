-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.flow_truncGen_mem_domain
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:50:23.010935+00:00
-- url     : https://prove2.me/submissions/5cec32fe-2899-40f5-ae84-43ed3a7d82e3

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.flow_truncGen_mem_domain
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_truncGen_mem
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) {x : H} (hx : x ∈ V) :
    flow (truncGen T V hV) t x ∈ T.domain := hV (flow_truncGen_mem T V hV t hx)
