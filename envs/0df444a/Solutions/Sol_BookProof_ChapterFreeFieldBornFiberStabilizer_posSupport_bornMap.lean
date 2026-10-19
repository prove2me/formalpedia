-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberStabilizer.posSupport_bornMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:04.73799+00:00
-- url     : https://prove2.me/submissions/463956a8-85f9-4e11-9ca4-bbcf84bd13ee

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — solution of BookProof.ChapterFreeFieldBornFiberStabilizer.posSupport_bornMap
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberStabilizer
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
    posSupport (bornMap x) = Finset.univ.filter (fun k => x k ≠ 0) := by

      ext k; simp only [posSupport, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq];
      unfold bornMap; simp [ sq_pos_iff ] ;
