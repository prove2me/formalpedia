-- Prove2me | solution 1 for BookProof.ChapterBornMeasure.bornMeasure_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:30:46.483136+00:00
-- url     : https://prove2.me/submissions/f78d542a-a930-48b5-a22d-ebcc2f7146fc

-- Generated from ChapterBornMeasure.lean — solution of BookProof.ChapterBornMeasure.bornMeasure_apply
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure



open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (psi : Lp ℂ 2 μ) {s : Set α} (hs : MeasurableSet s) :
    bornMeasure psi s = ∫⁻ x in s, ‖(psi : α → ℂ) x‖ₑ ^ 2 ∂μ := by

  rw [bornMeasure, withDensity_apply _ hs]
  rfl
