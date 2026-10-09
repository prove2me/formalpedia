-- Prove2me | solution 1 for BookProof.ChapterBornMeasure.bornMeasure_univ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:31:38.843557+00:00
-- url     : https://prove2.me/submissions/40e649b4-e25a-466f-95a2-b8e8aa78e3cb

-- Generated from ChapterBornMeasure.lean — solution of BookProof.ChapterBornMeasure.bornMeasure_univ
import Mathlib
import Definitions.Def_ChapterBornMeasure
import Theorems.Thm_BookProof_ChapterBornMeasure_bornMeasure_apply
import Theorems.Thm_BookProof_ChapterBornMeasure_lintegral_bornDensity
open BookProof.ChapterBornMeasure



open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) :
    bornMeasure psi Set.univ = 1 := by

  rw [bornMeasure_apply psi MeasurableSet.univ, Measure.restrict_univ,
    lintegral_bornDensity psi hpsi]
