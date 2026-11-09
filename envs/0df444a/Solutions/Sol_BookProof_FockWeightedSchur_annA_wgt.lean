-- Prove2me | solution 1 for BookProof.FockWeightedSchur.annA_wgt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:52:31.684616+00:00
-- url     : https://prove2.me/submissions/c64ae27a-9c7e-416c-9f6f-84ac910477c6

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.annA_wgt
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_wSym_up
import Theorems.Thm_BookProof_FockWeightedSchur_wgt_apply
import Theorems.Thm_BookProof_FockSecondQuantization_annA_apply
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
theorem solution (j : ℕ) (u : FockAlg) :
    annA j (wgt w u) = wgt w (annA j u) + ((w j ^ 2 : ℝ) : ℂ) • annA j u := by

  refine Finsupp.ext fun α => ?_
  rw [annA_apply, wgt_apply, Finsupp.add_apply, wgt_apply, annA_apply, Finsupp.smul_apply,
    annA_apply, smul_eq_mul, wSym_up]
  push_cast
  ring
