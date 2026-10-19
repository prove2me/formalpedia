-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.isPositive_shift_of_isSemibounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:47.598787+00:00
-- url     : https://prove2.me/submissions/cbd206d0-eecf-4ced-9361-43850e02ed21

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.isPositive_shift_of_isSemibounded
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
    (A : Dom →ₗ[ℂ] F) (hA : IsSemiboundedSelfAdjointExtension c H A) :
    IsPositiveSelfAdjointExtension (H + (c : ℂ) • D.subtype) (A + (c : ℂ) • Dom.subtype) := by

  obtain ⟨hagree, hsymA, hbelowA, hsa⟩ := hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨h, hx⟩ := hagree x
    refine ⟨h, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply, hx]
  · intro x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hsymA x y]
  · intro y
    rw [quadForm_shift]
    linarith [hbelowA y]
  · intro w u hw
    have hw' : ∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) (u - (c : ℂ) • w) := by
      intro v
      have hv := hw v
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        inner_add_left, inner_smul_left, Complex.conj_ofReal] at hv
      rw [inner_sub_right, inner_smul_right, ← hv]
      ring
    obtain ⟨h, hval⟩ := hsa w (u - (c : ℂ) • w) hw'
    refine ⟨h, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply, hval]
    module
