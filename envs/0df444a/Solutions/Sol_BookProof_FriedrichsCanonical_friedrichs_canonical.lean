-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.friedrichs_canonical
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:38:36.528968+00:00
-- url     : https://prove2.me/submissions/6dfde0b3-8242-4054-a240-3325b859601e

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.friedrichs_canonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Theorems.Thm_BookProof_FriedrichsCanonical_eq_zero_of_inner_coe_eq_zero
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.QgOuterFockFL
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open BookProof.FriedrichsCanonical in
theorem solution (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    {Dom' : Submodule ℂ F} (A' : Dom' →ₗ[ℂ] F)
    (hext : ∀ x : P.dom, ∃ h : (x : F) ∈ Dom', A' ⟨(x : F), h⟩ = P.op x)
    (hsym : SymmetricOn Dom' A') (hform : Dom' ≤ formDomain P)
    (x : F) (hx : x ∈ Dom') :
    ∃ h : x ∈ friedrichsDomain P, friedrichsOp P hdense ⟨x, h⟩ = A' ⟨x, hx⟩ := by
  obtain ⟨k, hk⟩ := hform hx
  have hk' : formExt P k = x := hk
  have hinj := friedrichsResolvent_injective P hdense
  set u : F := A' ⟨x, hx⟩ + x with hu
  have hR : formRiesz P u = k := by
    rw [← sub_eq_zero]
    apply eq_zero_of_inner_coe_eq_zero
    intro v
    have h1 : (inner ℂ (v : FormSpace P) (formRiesz P u) : ℂ) = inner ℂ (toAmbient v) u := by
      rw [← inner_conj_symm, formRiesz_spec, formExt_coe, inner_conj_symm]
    have h2 := inner_coe_eq P v k
    rw [hk'] at h2
    obtain ⟨hv, hAv⟩ := hext (toDom v)
    have hs := hsym ⟨_, hv⟩ ⟨x, hx⟩
    rw [inner_sub_right, h1, h2, hu, inner_add_right, inner_add_left, ← hAv]
    have : toAmbient v = ((toDom v : P.dom) : F) := rfl
    rw [this, hs]
    ring
  have hSx : friedrichsResolvent P u = x := by
    show formExt P (formRiesz P u) = x
    rw [hR, hk']
  refine ⟨⟨u, hSx⟩, ?_⟩
  show invShiftOperator (friedrichsResolvent P) hinj 1 ⟨x, _⟩ = _
  have hfin : u - ((1 : ℝ) : ℂ) • x = A' ⟨x, hx⟩ := by rw [hu]; simp
  rw [invShiftOperator_apply, preim_eq _ hinj _ hSx]
  exact hfin
