-- Prove2me | solution 1 for BookProof.FockSchur.up_apply_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T08:10:45.117246+00:00
-- url     : https://prove2.me/submissions/5941f54b-cf0f-4ce2-bde0-73b6577eeff6

-- Generated from ChapterFockSchurEsa.lean — solution of BookProof.FockSchur.up_apply'
import Mathlib
import Definitions.Def_ChapterFockSchurEsa
import Theorems.Thm_BookProof_FockSecondQuantization_up_of_ne
import Theorems.Thm_BookProof_FockSecondQuantization_up_self
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.YangMillsFriedrichs
open BookProof.FockSecondQuantization

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (j : ℕ) (α : Conf) (i : ℕ) : up j α i = α i + if i = j then 1 else 0 := by

  by_cases h : i = j
  · subst h; simp [up_self]
  · simp [up_of_ne _ h, h]
