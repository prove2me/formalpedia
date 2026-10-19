-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:56:56.75784+00:00
-- url     : https://prove2.me/submissions/e83b2772-c00e-4c1d-9f9d-0a007502abd3

-- Generated from ChapterAbelianCyclicCommutant.lean — solution of BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_conjRep_conjRepSymm
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_mem_multModelRep_iff
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_commutesWithContMult_conjRepSymm
import Theorems.Thm_BookProof_ChapterAbelianCyclicModel_cyclicRepUnitary_intertwines
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_comm
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralCommutant
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterAbelianCyclicCommutant



noncomputable section

open MeasureTheory Complex WeakDual


open BookProof.ChapterLinftyMultiplication BookProof.ChapterLinftyMaximalAbelian
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralCommutant
open BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterLinftyMultiplication


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange (repVec pi xi))

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange (repVec pi xi))

set_option maxHeartbeats 1000000 in
theorem solution : (repSet pi).centralizer = multModelRep pi xi hcyc := by

  apply Set.eq_of_subset_of_subset
  · intro S hS
    have hcomm : ∀ g : C(X, ℂ), pi g * S = S * pi g := fun g => hS _ ⟨g, rfl⟩
    rw [mem_multModelRep_iff]
    exact contCommutant_mem_multAlgebra (commutesWithContMult_conjRepSymm pi xi hcyc hcomm)
  · rintro S hS R ⟨g, rfl⟩
    obtain ⟨psi, hpsi, hSeq⟩ := (mem_multModelRep_iff pi xi hcyc S).1 hS
    have hS' : S = conjRep pi xi hcyc (multOp psi hpsi) := by
      rw [← hSeq, conjRep_conjRepSymm]
    subst hS'
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.mul_apply, conjRep_apply]
    have hcomm := multOp_comm (μ := repMeasure pi xi) psi (fun x => g x) hpsi
      (contMemLpTop _ g)
    have hkey := congrArg
      (fun P : Lp ℂ 2 (repMeasure pi xi) →L[ℂ] Lp ℂ 2 (repMeasure pi xi) =>
        P ((cyclicRepUnitary pi xi hcyc).symm v)) hcomm
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hkey
    have h1 : cyclicRepUnitary pi xi hcyc
          (mulRep (repMeasure pi xi) g
            (multOp psi hpsi ((cyclicRepUnitary pi xi hcyc).symm v)))
        = pi g (cyclicRepUnitary pi xi hcyc
            (multOp psi hpsi ((cyclicRepUnitary pi xi hcyc).symm v))) :=
      cyclicRepUnitary_intertwines pi xi hcyc g _
    have h2 : (cyclicRepUnitary pi xi hcyc).symm (pi g v)
        = mulRep (repMeasure pi xi) g ((cyclicRepUnitary pi xi hcyc).symm v) := by
      have := cyclicRepUnitary_intertwines pi xi hcyc g ((cyclicRepUnitary pi xi hcyc).symm v)
      rw [LinearIsometryEquiv.apply_symm_apply] at this
      rw [← this, LinearIsometryEquiv.symm_apply_apply]
    rw [h2, ← h1]
    exact congrArg (cyclicRepUnitary pi xi hcyc) hkey.symm
