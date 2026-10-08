-- Prove2me | solution 1 for BookProof.BddBelowFiberSumEsa.qgFiberSum_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:46:15.686841+00:00
-- url     : https://prove2.me/submissions/2097ee40-a235-41a0-9d3e-63dc50e33feb

-- Generated from ChapterBddBelowFiberSumEsa.lean — solution of BookProof.BddBelowFiberSumEsa.qgFiberSum_esa
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_essentiallySelfAdjoint_of_nonneg
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_contDiff_qgFiberV
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_qgFiberV_nonneg
open BookProof.BddBelowFiberSumEsa




open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) {d : ℕ} (omega : Fin d → ℝ) :
    EssentiallySelfAdjointOn (fiberCore (Option (Fin d)))
      (fiberSumHam (qgFiberV M alpha omega) (contDiff_qgFiberV M alpha omega)) := fiberSumHam_essentiallySelfAdjoint_of_nonneg _ _ (qgFiberV_nonneg halpha omega)
