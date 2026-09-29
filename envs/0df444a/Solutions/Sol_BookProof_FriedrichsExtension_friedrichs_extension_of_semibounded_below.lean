-- Prove2me | solution 1 for BookProof.FriedrichsExtension.friedrichs_extension_of_semibounded_below
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:40:59.900377+00:00
-- url     : https://prove2.me/submissions/f53f4d5f-a40e-400f-8552-321e3e5f6a17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFriedrichsExtension.lean — solution of BookProof.FriedrichsExtension.friedrichs_extension_of_semibounded_below
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists
open BookProof.FriedrichsExtension




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsSemiboundedSelfAdjointExtension c H A := by

  -- the shifted operator `H + c` is positive
  set Hc : D →ₗ[ℂ] F := H + (c : ℂ) • D.subtype with hHc
  have hshift : ∀ x : D, quadForm Hc x = quadForm H x + c * ‖(x : F)‖ ^ 2 := by
    intro x
    simp only [hHc, quadForm, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_add_right, inner_smul_right, Complex.add_re]
    congr 1
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hcsym : SymmetricOn D Hc := by
    intro x y
    simp only [hHc, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hsym x y]
  have hcpos : ∀ x : D, 0 ≤ quadForm Hc x := by
    intro x
    rw [hshift]
    linarith [hbelow x]
  obtain ⟨Dom, A', hA'⟩ := friedrichs_extension_exists ⟨D, Hc, hcsym, hcpos⟩ hdense
  obtain ⟨hagree, hsymA, hposA, hsa⟩ := hA'
  refine ⟨Dom, A' - (c : ℂ) • Dom.subtype, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨h, hx⟩ := hagree x
    refine ⟨h, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, hx, hHc,
      LinearMap.add_apply]
    module
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hsymA x y]
  · intro y
    have h : quadForm (A' - (c : ℂ) • Dom.subtype) y = quadForm A' y - c * ‖(y : F)‖ ^ 2 := by
      simp only [quadForm, LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        inner_sub_right, inner_smul_right, Complex.sub_re]
      congr 1
      rw [inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    rw [h]
    linarith [hposA y]
  · intro w u hw
    have hw' : ∀ v : Dom, (inner ℂ (A' v) w : ℂ) = inner ℂ (v : F) (u + (c : ℂ) • w) := by
      intro v
      have := hw v
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        inner_sub_left, inner_smul_left, Complex.conj_ofReal] at this
      rw [inner_add_right, inner_smul_right, ← this]
      ring
    obtain ⟨h, hval⟩ := hsa w (u + (c : ℂ) • w) hw'
    refine ⟨h, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, hval]
    module
