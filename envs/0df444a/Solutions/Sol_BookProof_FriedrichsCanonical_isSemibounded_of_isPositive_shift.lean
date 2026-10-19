-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:46.464729+00:00
-- url     : https://prove2.me/submissions/8b47b033-a3df-4fca-9fd3-5842fed64025

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
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
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {Dom : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ)
    (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension (H + (c : ℂ) • D.subtype) A) :
    IsSemiboundedSelfAdjointExtension c H (A - (c : ℂ) • Dom.subtype) := by

  obtain ⟨hagree, hsymA, hposA, hsa⟩ := hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨h, hx⟩ := hagree x
    refine ⟨h, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, hx,
      LinearMap.add_apply]
    module
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hsymA x y]
  · intro y
    have h : quadForm (A - (c : ℂ) • Dom.subtype) y = quadForm A y - c * ‖(y : F)‖ ^ 2 := by
      have h1 := quadForm_shift A (-c) y
      simp only [Complex.ofReal_neg, neg_smul, neg_mul, ← sub_eq_add_neg] at h1
      exact h1
    rw [h]
    linarith [hposA y]
  · intro w u hw
    have hw' : ∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) (u + (c : ℂ) • w) := by
      intro v
      have hv := hw v
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        inner_sub_left, inner_smul_left, Complex.conj_ofReal] at hv
      rw [inner_add_right, inner_smul_right, ← hv]
      ring
    obtain ⟨h, hval⟩ := hsa w (u + (c : ℂ) • w) hw'
    refine ⟨h, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, hval]
    module
