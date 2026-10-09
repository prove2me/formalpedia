-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.exactStates_le_physicalStates
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:44:07.721296+00:00
-- url     : https://prove2.me/submissions/a00f8e28-2dd2-4d86-8c7b-248789146492

-- Generated from ChapterBrstReducedTransfer.lean — solution of BookProof.BrstReducedTransfer.exactStates_le_physicalStates
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
open BookProof.BrstReducedTransfer




open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (Om : H →L[ℂ] H)

set_option maxHeartbeats 1000000 in
theorem solution (hnil : ∀ x, Om (Om x) = 0) :
    exactStates Om ≤ physicalStates Om := by

  refine Submodule.topologicalClosure_minimal _ ?_ Om.isClosed_ker
  rintro x ⟨y, rfl⟩
  exact hnil y
