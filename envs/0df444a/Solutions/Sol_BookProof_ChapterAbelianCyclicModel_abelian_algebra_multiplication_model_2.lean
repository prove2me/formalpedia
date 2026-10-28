-- Prove2me | solution 2 for BookProof.ChapterAbelianCyclicModel.abelian_algebra_multiplication_model
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:21:40.949966+00:00
-- url     : https://prove2.me/submissions/f65c5ac0-9bd8-41ea-b29d-38236156cbeb

import Definitions.Def_ChapterAbelianGelfandModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
import Theorems.Thm_BookProof_ChapterAbelianCyclicModel_cyclic_representation_multiplication_model_inc
-- Generated from ChapterAbelianCyclicModel.lean — theorem solution
open BookProof.ChapterAbelianCyclicModel


open MeasureTheory Complex WeakDual
open scoped ComplexOrder


open BookProof.ChapterAbelianGelfandModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)

variable (hcyc : DenseRange (repVec pi xi))
variable {A : Type*} [CommCStarAlgebra A]
theorem solution (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)
    (hxi : ‖xi‖ = 1) (hcyc : DenseRange fun a : A => rho a xi) :
    ∃ (mu : Measure (characterSpace ℂ A)) (_ : IsProbabilityMeasure mu)
      (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      ∀ (a : A) (u : Lp ℂ 2 mu), U (mulRep mu (gelfandModel A a) u) = rho a (U u) := by
  have hcyc' : DenseRange (repVec (gelfandRep rho) xi) := by
    refine Dense.mono ?_ hcyc
    rintro _ ⟨a, rfl⟩
    refine ⟨gelfandModel A a, ?_⟩
    simp [repVec, gelfandRep_gelfandModel]
  obtain ⟨mu, hmu, U, h1, -⟩ :=
    cyclic_representation_multiplication_model_inc (gelfandRep rho) xi hcyc' hxi
  exact ⟨mu, hmu, U, fun a u => by rw [h1, gelfandRep_gelfandModel]⟩
