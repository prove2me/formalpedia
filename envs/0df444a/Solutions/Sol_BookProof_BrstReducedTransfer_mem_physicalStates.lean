-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.mem_physicalStates
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:34:41.2806+00:00
-- url     : https://prove2.me/submissions/e3fb8428-3c2f-471c-aaf5-8d852136e83a

-- Generated from ChapterBrstReducedTransfer.lean — solution of BookProof.BrstReducedTransfer.mem_physicalStates
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
open BookProof.BrstReducedTransfer




open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (Om : H →L[ℂ] H)

set_option maxHeartbeats 1000000 in
theorem solution {x : H} : x ∈ physicalStates Om ↔ Om x = 0 := Iff.rfl
