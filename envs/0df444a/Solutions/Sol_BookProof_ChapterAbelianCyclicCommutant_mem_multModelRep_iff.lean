-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicCommutant.mem_multModelRep_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:00:14.175825+00:00
-- url     : https://prove2.me/submissions/f95b74bf-f99e-4637-aff2-a69e4d8cfdec

-- Generated from ChapterAbelianCyclicCommutant.lean — solution of BookProof.ChapterAbelianCyclicCommutant.mem_multModelRep_iff
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_conjRep_conjRepSymm
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_conjRepSymm_conjRep
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
theorem solution (S : H →L[ℂ] H) :
    S ∈ multModelRep pi xi hcyc ↔
      conjRepSymm pi xi hcyc S ∈ multAlgebra (repMeasure pi xi) := by

  constructor
  · rintro ⟨A, hA, rfl⟩
    rwa [conjRepSymm_conjRep]
  · intro h
    exact ⟨conjRepSymm pi xi hcyc S, h, conjRep_conjRepSymm pi xi hcyc S⟩
