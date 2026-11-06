-- Prove2me | solution 1 for BookProof.ChapterG.haarAverage_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T14:17:10.113207+00:00
-- url     : https://prove2.me/submissions/a8790a3b-3559-4456-ad54-cfd5ecbf48b4

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.haarAverage_one
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix
open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

set_option maxHeartbeats 1000000 in

theorem solution : haarAverage (μG := μG) (X := X) (fun _ => 1) = fun _ => 1 := by
  funext x
  simp only [haarAverage, integral_const]
  simp
