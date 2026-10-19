-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicModel.integral_repMeasure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:40:33.381587+00:00
-- url     : https://prove2.me/submissions/3e47e0b0-af71-4084-a2c5-139a6be55c04

-- Generated from ChapterAbelianCyclicModel.lean — solution of BookProof.ChapterAbelianCyclicModel.integral_repMeasure
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_integral_stateMeasure
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
theorem solution (f : C(X, ℂ)) :
    inner ℂ xi (pi f xi) = ∫ x, f x ∂(repMeasure pi xi) := integral_stateMeasure (repState pi xi) (repState_pos pi xi) f
