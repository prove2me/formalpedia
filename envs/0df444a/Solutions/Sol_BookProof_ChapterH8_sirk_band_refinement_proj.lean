-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_band_refinement_proj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:54:29.73403+00:00
-- url     : https://prove2.me/submissions/6351d0a4-ade9-427e-9a19-1fe5c3cd58a0

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.sirk_band_refinement_proj
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_adjoint_comp_self_of_nested
import Theorems.Thm_BookProof_ChapterH8_sirk_band_refinement
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH8



open ContinuousLinearMap

noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH4

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y)
    (hinvm : ∀ x : G, ∃ y : G, X (Vm x) = Vm y)
    (k : ℕ) (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vn ((adjoint Vn) (Vm (((compress Vm X) ^ k) ((adjoint Vm) v))))
      = Vn (((compress Vn X) ^ k) ((adjoint Vn) v)) := by

  have hVn : (adjoint Vn).comp Vn = ContinuousLinearMap.id ℂ F :=
    adjoint_comp_self_of_nested Vn Vm J hJ hVm hJJ
  have href := sirk_band_refinement Vn Vm J X hJ hVm hJJ hinvn hinvm k v hv
  rw [href]
  have := congrArg (fun f : F →L[ℂ] F => f (((compress Vn X) ^ k) ((adjoint Vn) v))) hVn
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq] at this
  rw [this]
