-- Prove2me | solution 1 for BookProof.ChapterBornMeasure.bornMeasure_absolutelyContinuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:30:59.316335+00:00
-- url     : https://prove2.me/submissions/bda77efe-1d27-4ad4-8238-85f304587164

-- Generated from ChapterBornMeasure.lean — solution of BookProof.ChapterBornMeasure.bornMeasure_absolutelyContinuous
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure



open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (psi : Lp ℂ 2 μ) : bornMeasure psi ≪ μ := withDensity_absolutelyContinuous _ _
