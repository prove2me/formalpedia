-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T18:56:22.972089+00:00
-- url     : https://prove2.me/submissions/c7f94f4b-d51f-4ba2-bbbf-6a3b27b2040c

-- Generated from ChapterAbelianCyclicCommutant.lean — solution of BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative_inc
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_conjRep_mul
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_centralizer_repSet
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


set_option maxHeartbeats 1000000 in
include hcyc in
theorem solution {S R : H →L[ℂ] H}
    (hS : S ∈ (repSet pi).centralizer) (hR : R ∈ (repSet pi).centralizer) :
    S * R = R * S := by

  rw [centralizer_repSet pi xi hcyc] at hS hR
  obtain ⟨A, hA, rfl⟩ := hS
  obtain ⟨B, hB, rfl⟩ := hR
  rw [← conjRep_mul, ← conjRep_mul, multAlgebra_comm hA hB]
