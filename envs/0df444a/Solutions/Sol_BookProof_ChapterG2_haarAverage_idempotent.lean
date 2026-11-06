-- Prove2me | solution 1 for BookProof.ChapterG2.haarAverage_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:28:01.788047+00:00
-- url     : https://prove2.me/submissions/1f97cfb9-a245-4a7c-a38a-fc5576131698

import Definitions.Def_ChapterG2
import Definitions.Def_ChapterG
import Theorems.Thm_BookProof_ChapterG_haarAverage_of_invariant
import Theorems.Thm_BookProof_ChapterG_haarAverage_smul

open BookProof.ChapterG BookProof.ChapterG2
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem solution [MeasurableMul G] (f : X → ℝ) :
    haarAverage (μG := μG) (haarAverage (μG := μG) f) = haarAverage (μG := μG) f := by
  exact haarAverage_of_invariant (haarAverage (μG := μG) f) (haarAverage_smul f)
