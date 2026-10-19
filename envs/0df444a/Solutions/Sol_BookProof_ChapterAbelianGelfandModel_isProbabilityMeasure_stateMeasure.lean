-- Prove2me | solution 1 for BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_stateMeasure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:48:23.820828+00:00
-- url     : https://prove2.me/submissions/7871f13e-4ef3-47ec-be2e-0cd42dfcc73b

-- Generated from ChapterAbelianGelfandModel.lean — solution of BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_stateMeasure
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterA3b
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

set_option maxHeartbeats 1000000 in
theorem solution (hone : psi 1 = 1) :
    IsProbabilityMeasure (stateMeasure psi hpos) := by

  have hLone : realPartFunctional psi 1 = 1 := by
    have h : toC (1 : C(X, ℝ)) = (1 : C(X, ℂ)) := by ext x; simp
    simp [realPartFunctional, h, hone]
  exact isProbabilityMeasure_rieszStateMeasure _ _ hLone
