-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:56:57.764404+00:00
-- url     : https://prove2.me/submissions/2a97e31a-adcf-41c5-b3d8-7c0bdd00ea15

-- Generated from ChapterAbelianCyclicCommutant.lean — solution of BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_conjRep_mul
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_mem_multModelRep_iff
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

set_option maxHeartbeats 1000000 in
theorem solution :
    (multModelRep pi xi hcyc).centralizer = multModelRep pi xi hcyc := by

  apply Set.eq_of_subset_of_subset
  · intro S hS
    rw [mem_multModelRep_iff]
    rw [← centralizer_multAlgebra (μ := repMeasure pi xi)]
    intro A hA
    have hmem : conjRep pi xi hcyc A ∈ multModelRep pi xi hcyc := ⟨A, hA, rfl⟩
    have h := hS _ hmem
    refine ContinuousLinearMap.ext fun u => ?_
    have h2 := congrArg (fun P : H →L[ℂ] H => P (cyclicRepUnitary pi xi hcyc u)) h
    simp only [ContinuousLinearMap.mul_apply, conjRep_apply,
      LinearIsometryEquiv.symm_apply_apply] at h2
    simp only [ContinuousLinearMap.mul_apply, conjRepSymm_apply]
    have h3 := congrArg (cyclicRepUnitary pi xi hcyc).symm h2
    rwa [LinearIsometryEquiv.symm_apply_apply] at h3
  · rintro S hS R ⟨A, hA, rfl⟩
    obtain ⟨B, hB, rfl⟩ := hS
    rw [← conjRep_mul, ← conjRep_mul, multAlgebra_comm hA hB]
