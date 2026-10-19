-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.semibounded_friedrichs_unique
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T10:35:18.017287+00:00
-- url     : https://prove2.me/submissions/46244f3e-e9ca-462d-a647-7e2433ffcf07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.semibounded_friedrichs_unique
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichs_unique_selfAdjoint
import Theorems.Thm_BookProof_FriedrichsCanonical_isPositive_shift_of_isSemibounded
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (hdense : Dense (D : Set F))
    {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F)
    (hA' : IsSemiboundedSelfAdjointExtension c H A')
    (hform : Dom' ≤ formDomain (shiftedPosSymOp H hsym c hbelow)) :
    Dom' = friedrichsDomain (shiftedPosSymOp H hsym c hbelow) ∧
      ∀ (x : F) (hx : x ∈ Dom')
        (hx' : x ∈ friedrichsDomain (shiftedPosSymOp H hsym c hbelow)),
        A' ⟨x, hx⟩ = semiboundedFriedrichsOp H hsym c hbelow hdense ⟨x, hx'⟩ := by

  obtain ⟨hdom, hval⟩ := friedrichs_unique_selfAdjoint (shiftedPosSymOp H hsym c hbelow) hdense
    (A' + (c : ℂ) • Dom'.subtype) (isPositive_shift_of_isSemibounded H c A' hA') hform
  refine ⟨hdom, ?_⟩
  intro x hx hx'
  have h := hval x hx hx'
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply] at h
  simp only [semiboundedFriedrichsOp, LinearMap.sub_apply, LinearMap.smul_apply,
    Submodule.subtype_apply, ← h]
  module
