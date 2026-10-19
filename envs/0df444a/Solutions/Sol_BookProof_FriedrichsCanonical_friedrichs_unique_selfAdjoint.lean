-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T10:34:59.877903+00:00
-- url     : https://prove2.me/submissions/bbef5de4-8746-44ce-8f7b-498b60a9af0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_symmetricOn
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichs_canonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.YangMillsFriedrichs

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F)
    (hA' : IsPositiveSelfAdjointExtension P.op A') (hform : Dom' ≤ formDomain P) :
    Dom' = friedrichsDomain P ∧
      ∀ (x : F) (hx : x ∈ Dom') (hx' : x ∈ friedrichsDomain P),
        A' ⟨x, hx⟩ = friedrichsOp P hdense ⟨x, hx'⟩ := by

  obtain ⟨hext, hsym, -, hcrit⟩ := hA'
  have hsub : ∀ (x : F) (hx : x ∈ Dom'), ∃ h : x ∈ friedrichsDomain P,
      friedrichsOp P hdense ⟨x, h⟩ = A' ⟨x, hx⟩ :=
    fun x hx => friedrichs_canonical P hdense A' hext hsym hform x hx
  have hle : Dom' ≤ friedrichsDomain P := fun x hx => (hsub x hx).choose
  have hagree : ∀ (x : F) (hx : x ∈ Dom') (hx' : x ∈ friedrichsDomain P),
      A' ⟨x, hx⟩ = friedrichsOp P hdense ⟨x, hx'⟩ := by
    intro x hx hx'
    exact ((hsub x hx).choose_spec).symm
  refine ⟨le_antisymm hle ?_, hagree⟩
  -- the converse inclusion: a self-adjoint operator has no proper symmetric extension
  intro w hw
  have hpair : ∀ v : Dom', (inner ℂ (A' v) w : ℂ)
      = inner ℂ (v : F) (friedrichsOp P hdense ⟨w, hw⟩) := by
    intro v
    have hv' : (v : F) ∈ friedrichsDomain P := hle v.2
    have h1 : (A' v : F) = friedrichsOp P hdense ⟨(v : F), hv'⟩ := by
      have := hagree (v : F) v.2 hv'
      simpa using this
    rw [h1]
    exact friedrichsOp_symmetricOn P hdense ⟨(v : F), hv'⟩ ⟨w, hw⟩
  exact (hcrit w (friedrichsOp P hdense ⟨w, hw⟩) hpair).choose
