-- Prove2me | solution 1 for BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T18:56:25.462953+00:00
-- url     : https://prove2.me/submissions/074828ef-e71c-425c-af80-2beffea29fe8

-- Generated from ChapterAbelianGelfandModel.lean — solution of BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_inc
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_isProbabilityMeasure_stateMeasure
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_integral_stateMeasure
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterAbelianGelfandModel



open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder


open BookProof.ChapterLinftyMultiplication

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))

set_option maxHeartbeats 1000000 in
include hpos in
theorem solution (hone : psi 1 = 1) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu :=
  ⟨stateMeasure psi hpos, isProbabilityMeasure_stateMeasure psi hpos hone,
      integral_stateMeasure psi hpos⟩
