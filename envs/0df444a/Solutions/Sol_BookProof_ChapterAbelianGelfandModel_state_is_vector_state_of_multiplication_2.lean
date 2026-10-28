-- Prove2me | solution 2 for BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:20:13.831989+00:00
-- url     : https://prove2.me/submissions/107bf614-21fb-4d5e-9cd7-04606b91cf84

import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_integral_stateMeasure
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_isProbabilityMeasure_stateMeasure
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_norm_oneVec
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_inner_oneVec_mulRep
-- Generated from ChapterAbelianGelfandModel.lean — theorem solution
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
variable (A : Type*) [CommCStarAlgebra A]
variable {A}
theorem solution (phi : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ phi (star a * a)) (hone : phi 1 = 1) :
    ∃ mu : Measure (characterSpace ℂ A), ∃ _ : IsProbabilityMeasure mu,
      ‖oneVec mu‖ = 1 ∧
      ∀ a : A, phi a = inner ℂ (oneVec mu) (multiplicationRep mu a (oneVec mu)) := by
  let G := gelfandModel A
  let psi' : C(characterSpace ℂ A, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => phi (G.symm g)
      map_add' := by intro f g; simp
      map_smul' := by intro c f; simp }
  have hpos' : ∀ g : C(characterSpace ℂ A, ℂ), 0 ≤ psi' (star g * g) := by
    intro g
    show 0 ≤ phi (G.symm (star g * g))
    rw [map_mul, map_star]
    exact hpos _
  have hone' : psi' 1 = 1 := by
    show phi (G.symm 1) = 1
    rw [map_one]
    exact hone
  haveI := isProbabilityMeasure_stateMeasure psi' hpos' hone'
  refine ⟨stateMeasure psi' hpos', inferInstance, norm_oneVec _, fun a => ?_⟩
  have h1 := integral_stateMeasure psi' hpos' (G a)
  have h2 := inner_oneVec_mulRep (stateMeasure psi' hpos') (G a)
  have h3 : psi' (G a) = phi a := by
    show phi (G.symm (G a)) = phi a
    rw [StarAlgEquiv.symm_apply_apply]
  have h4 : multiplicationRep (stateMeasure psi' hpos') a = mulRep (stateMeasure psi' hpos') (G a) := by
    simp only [multiplicationRep, StarAlgHom.comp_apply, mulRepHom_apply]
    rfl
  rw [h4]
  exact h3.symm.trans (h1.trans h2.symm)
