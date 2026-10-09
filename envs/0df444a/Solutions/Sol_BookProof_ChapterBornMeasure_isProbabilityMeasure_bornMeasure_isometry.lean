-- Prove2me | solution 1 for BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure_isometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:31:53.513717+00:00
-- url     : https://prove2.me/submissions/044ff136-45d1-4eb4-8d64-4724cc4f0153

-- Generated from ChapterBornMeasure.lean — solution of BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure_isometry
import Mathlib
import Definitions.Def_ChapterBornMeasure
import Theorems.Thm_BookProof_ChapterBornMeasure_isProbabilityMeasure_bornMeasure
open BookProof.ChapterBornMeasure



open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) : IsProbabilityMeasure (bornMeasure (U psi)) := isProbabilityMeasure_bornMeasure _ (by rw [U.norm_map, hpsi])
