-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T07:40:01.447503+00:00
-- url     : https://prove2.me/submissions/5901aebc-469e-4405-a3e4-a413dafd96ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAbelianCyclicCommutant.lean — solution of BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_centralizer_repSet
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_bicommutant_repSet
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_commutant_repSet_isCommutative
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_repSet_gelfandRep
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_denseRange_repVec_gelfandRep
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
theorem solution (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)
    (hcyc : DenseRange fun a : A => rho a xi) :
    (Set.range fun a : A => rho a).centralizer.centralizer
        = (Set.range fun a : A => rho a).centralizer ∧
      ∀ S R : H →L[ℂ] H, S ∈ (Set.range fun a : A => rho a).centralizer →
        R ∈ (Set.range fun a : A => rho a).centralizer → S * R = R * S := by

  have hcyc' := denseRange_repVec_gelfandRep hcyc
  have hset := repSet_gelfandRep rho
  constructor
  · rw [← hset, bicommutant_repSet (gelfandRep rho) xi hcyc',
      centralizer_repSet (gelfandRep rho) xi hcyc']
  · intro S R hS hR
    rw [← hset] at hS hR
    exact commutant_repSet_isCommutative (gelfandRep rho) hS hR
