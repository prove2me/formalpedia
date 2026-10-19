-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicCommutant.denseRange_repVec_gelfandRep
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:00:19.132915+00:00
-- url     : https://prove2.me/submissions/e9a86e29-1f66-4576-83b7-663202e88c30

-- Generated from ChapterAbelianCyclicCommutant.lean — solution of BookProof.ChapterAbelianCyclicCommutant.denseRange_repVec_gelfandRep
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
theorem solution {rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {xi : H}
    (hcyc : DenseRange fun a : A => rho a xi) :
    DenseRange (repVec (gelfandRep rho) xi) := by

  have hrange : Set.range (repVec (gelfandRep rho) xi) = Set.range fun a : A => rho a xi := by
    ext v
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨(gelfandModel A).symm f, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gelfandModel A a, by simp [repVec]⟩
  rw [DenseRange, hrange]
  exact hcyc
