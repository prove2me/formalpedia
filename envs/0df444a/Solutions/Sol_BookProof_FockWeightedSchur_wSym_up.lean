-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wSym_up
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:52:06.759803+00:00
-- url     : https://prove2.me/submissions/a8c8c894-f30b-4db3-b9ca-715aa9540139

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wSym_up
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_wdeg_up
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.FockSecondQuantization

noncomputable section

variable {w : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (j : ℕ) (α : Conf) : wSym w (up j α) = wSym w α + w j ^ 2 := by

  simp only [wSym, wdeg_up]; ring
