-- Prove2me | solution 1 for BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:48:57.395959+00:00
-- url     : https://prove2.me/submissions/1f1e43ac-8b04-4569-a91b-3a2c1a1aa102

-- Generated from ChapterAbelianGelfandModel.lean — solution of BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_oneVec_coeFn
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterAbelianGelfandModel



open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder


open BookProof.ChapterLinftyMultiplication

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {X : Type*} [TopologicalSpace X]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))
variable {X : Type*} [MeasurableSpace X] (mu : Measure X)
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (mu : Measure X)

set_option maxHeartbeats 1000000 in
theorem solution [IsFiniteMeasure mu] (f : C(X, ℂ)) :
    inner ℂ (oneVec mu) (mulRep mu f (oneVec mu)) = ∫ x, f x ∂mu := by

  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [oneVec_coeFn mu, mulRep_coeFn mu f (oneVec mu)] with x h1 h2
  simp [h1, h2]
