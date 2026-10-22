-- Prove2me | solution 1 for BookProof.BddBelowFiberSumEsa.qgFiberSum_nonneg_form
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:38:35.646966+00:00
-- url     : https://prove2.me/submissions/f17fbcaf-f405-4960-b82b-fe46f709c90c

-- Generated from ChapterBddBelowFiberSumEsa.lean — solution of BookProof.BddBelowFiberSumEsa.qgFiberSum_nonneg_form
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_nonneg_form
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_contDiff_qgFiberV
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_qgFiberV_nonneg
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterBddBelowWallEsa
open BookProof.BddBelowFiberSumEsa




open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded
open BookProof.BddBelowWallEsa BookProof.WallEsaSemibounded BookProof.DirectSumEsa
open BookProof.WallEsaSemibounded

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) {d : ℕ} (omega : Fin d → ℝ) :
    SemiboundedBelowOn (fiberCore (Option (Fin d)))
      (fiberSumHam (qgFiberV M alpha omega) (contDiff_qgFiberV M alpha omega)) 0 := fiberSumHam_nonneg_form _ _ (qgFiberV_nonneg halpha omega)
