-- Prove2me | solution 1 for BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T02:07:57.206745+00:00
-- url     : https://prove2.me/submissions/43dbb4f2-6a74-40f8-a19e-def825171350

-- Generated from ChapterSirkSingleTimeShift.lean — solution of BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Theorems.Thm_BookProof_SirkSingleTime_strongResAt_of_ne_zero
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
open BookProof.SirkSingleTime



open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

set_option maxHeartbeats 1000000 in
theorem solution {l : ℝ} (hl : l ≠ 0)
    (h : StrongResAt T S l) : StrongResolventConvergence T S := fun y => strongResAt_of_ne_zero hl one_ne_zero h y
