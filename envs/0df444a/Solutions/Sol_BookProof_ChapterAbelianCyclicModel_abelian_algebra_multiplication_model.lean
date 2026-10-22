-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicModel.abelian_algebra_multiplication_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T07:40:02.821329+00:00
-- url     : https://prove2.me/submissions/dcf0ab70-5a5a-4821-874d-f6b8319bfd24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAbelianCyclicModel.lean — solution of BookProof.ChapterAbelianCyclicModel.abelian_algebra_multiplication_model
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
import Theorems.Thm_BookProof_ChapterAbelianCyclicModel_cyclic_representation_multiplication_model
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
variable (hcyc : DenseRange (repVec pi xi))
variable {A : Type*} [CommCStarAlgebra A]

set_option maxHeartbeats 1000000 in
theorem solution (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)
    (hxi : ‖xi‖ = 1) (hcyc : DenseRange fun a : A => rho a xi) :
    ∃ (mu : Measure (characterSpace ℂ A)) (_ : IsProbabilityMeasure mu)
      (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      ∀ (a : A) (u : Lp ℂ 2 mu), U (mulRep mu (gelfandModel A a) u) = rho a (U u) := by

  have hrange : Set.range (repVec (gelfandRep rho) xi) = Set.range fun a : A => rho a xi := by
    ext v
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨(gelfandModel A).symm f, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gelfandModel A a, by simp [repVec]⟩
  have hcyc' : DenseRange (repVec (gelfandRep rho) xi) := by
    rw [DenseRange, hrange]
    exact hcyc
  obtain ⟨mu, hmu, U, hU, -⟩ :=
    cyclic_representation_multiplication_model (gelfandRep rho) xi hxi
  refine ⟨mu, hmu, U, fun a u => ?_⟩
  rw [hU (gelfandModel A a) u, gelfandRep_gelfandModel]
