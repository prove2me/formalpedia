-- Prove2me | solution 1 for BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:31:39.917531+00:00
-- url     : https://prove2.me/submissions/dc2fb837-e16a-4ea9-9ea7-e8f50c8dc276

-- Generated from ChapterBornMeasure.lean — solution of BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure
import Mathlib
import Definitions.Def_ChapterBornMeasure
import Theorems.Thm_BookProof_ChapterBornMeasure_bornMeasure_univ
open BookProof.ChapterBornMeasure



open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) :
    IsProbabilityMeasure (bornMeasure psi) := ⟨bornMeasure_univ psi hpsi⟩
