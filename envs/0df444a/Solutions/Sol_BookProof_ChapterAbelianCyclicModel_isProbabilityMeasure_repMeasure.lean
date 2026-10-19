-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicModel.isProbabilityMeasure_repMeasure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:40:32.159128+00:00
-- url     : https://prove2.me/submissions/52bf0722-b363-481d-903a-446245dac91b

-- Generated from ChapterAbelianCyclicModel.lean — solution of BookProof.ChapterAbelianCyclicModel.isProbabilityMeasure_repMeasure
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
import Theorems.Thm_BookProof_ChapterAbelianCyclicModel_repState_one
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_isProbabilityMeasure_stateMeasure
import Definitions.Def_ChapterAbelianGelfandModel
open BookProof.ChapterAbelianCyclicModel



open MeasureTheory Complex WeakDual
open scoped ComplexOrder


open BookProof.ChapterAbelianGelfandModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)

set_option maxHeartbeats 1000000 in
theorem solution (hxi : ‖xi‖ = 1) :
    IsProbabilityMeasure (repMeasure pi xi) := isProbabilityMeasure_stateMeasure _ _ (repState_one pi xi hxi)
