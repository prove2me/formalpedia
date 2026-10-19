-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T18:56:28.208383+00:00
-- url     : https://prove2.me/submissions/e6bbfe08-ddea-4a7f-977b-dcd56906ab57

-- Generated from ChapterBrstReducedTransfer.lean — solution of BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_inc
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstReducedTransfer




open BookProof BookProof.ChapterStoneResolvent




variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) (Om : H →L[ℂ] H)
variable (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y))

set_option maxHeartbeats 1000000 in

include hcomm in
theorem solution (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) :
    T.stoneU t x ∈ physicalStates Om :=
  physicalStates_invariant (hcomm t) x hx

