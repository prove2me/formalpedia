-- Prove2me | solution 1 for BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T07:40:04.069002+00:00
-- url     : https://prove2.me/submissions/695f41c4-e884-4433-8fd0-38ca6ddc7b48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAbelianGelfandModel.lean — solution of BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_exists_probabilityMeasure_of_state
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_norm_oneVec
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_inner_oneVec_mulRep
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
variable (A : Type*) [CommCStarAlgebra A]
variable {A}

set_option maxHeartbeats 1000000 in
theorem solution (phi : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ phi (star a * a)) (hone : phi 1 = 1) :
    ∃ mu : Measure (characterSpace ℂ A), ∃ _ : IsProbabilityMeasure mu,
      ‖oneVec mu‖ = 1 ∧
      ∀ a : A, phi a = inner ℂ (oneVec mu) (multiplicationRep mu a (oneVec mu)) := by

  classical
  set G := gelfandModel A with hG
  set psi : C(characterSpace ℂ A, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => phi (G.symm g)
      map_add' := by intro g h; simp
      map_smul' := by intro c g; simp } with hpsi
  have hpsipos : ∀ g : C(characterSpace ℂ A, ℂ), 0 ≤ psi (star g * g) := by
    intro g
    have h : G.symm (star g * g) = star (G.symm g) * G.symm g := by
      rw [map_mul, map_star]
    simpa [hpsi, h] using hpos (G.symm g)
  have hpsione : psi 1 = 1 := by simpa [hpsi] using hone
  obtain ⟨mu, hmu, hint⟩ := exists_probabilityMeasure_of_state psi hpsione
  refine ⟨mu, hmu, norm_oneVec mu, ?_⟩
  intro a
  have h1 : phi a = psi (G a) := by simp [hpsi, hG]
  rw [h1, hint (G a), ← inner_oneVec_mulRep mu (G a)]
  rfl
