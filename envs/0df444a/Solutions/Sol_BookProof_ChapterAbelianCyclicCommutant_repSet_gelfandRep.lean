-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicCommutant.repSet_gelfandRep
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:00:17.999794+00:00
-- url     : https://prove2.me/submissions/0c4473dc-18dd-4376-b71c-17f54faa2407

-- Generated from ChapterAbelianCyclicCommutant.lean — solution of BookProof.ChapterAbelianCyclicCommutant.repSet_gelfandRep
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralCommutant
import Definitions.Def_ChapterAbelianCyclicModel
open BookProof.ChapterAbelianCyclicCommutant



noncomputable section

open MeasureTheory Complex WeakDual


open BookProof.ChapterLinftyMultiplication BookProof.ChapterLinftyMaximalAbelian
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralCommutant
open BookProof.ChapterAbelianCyclicModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange (repVec pi xi))

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange (repVec pi xi))
variable {A : Type*} [CommCStarAlgebra A]

set_option maxHeartbeats 1000000 in
theorem solution (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    repSet (gelfandRep rho) = Set.range fun a : A => rho a := by

  ext S
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨(gelfandModel A).symm f, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨gelfandModel A a, by simp⟩
