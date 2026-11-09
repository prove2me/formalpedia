-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wdeg_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:50:45.159541+00:00
-- url     : https://prove2.me/submissions/be2cc72a-8279-49bc-a11a-e8acc852603c

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wdeg_nonneg
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_wdeg_eq_sum
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
theorem solution (α : Conf) : 0 ≤ wdeg w α := by

  rw [wdeg_eq_sum (Finset.Subset.refl α.support)]
  refine Finset.sum_nonneg fun k _ => ?_
  have : (0:ℝ) ≤ w k ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (α k : ℝ) := Nat.cast_nonneg _
  positivity
