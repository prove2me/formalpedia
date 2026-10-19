-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card_mul_two_pow_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:03.543981+00:00
-- url     : https://prove2.me/submissions/991a00ef-72ea-4d57-ae83-749041315cee

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — solution of BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card_mul_two_pow_nonzero
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberStabilizer
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberStabilizer_signStab_card
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberBounds
open BookProof.ChapterFreeFieldBornFiberStabilizer



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (x : EuclideanSpace ℝ (Fin n)) :
    (signStab x).card * 2 ^ (Finset.univ.filter (fun k => x k ≠ 0)).card = 2 ^ n := by

      rw [ signStab_card, ← pow_add, Finset.card_filter_add_card_filter_not ];
      norm_num
