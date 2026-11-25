-- Prove2me | solution 1 for Formalism.QuantumDeterminants.weyl_functional_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:27:28.604522+00:00
-- url     : https://prove2.me/submissions/4fe428b7-c255-4c35-8b34-f5edfda7c26b

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_reg_of_mem
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_coef
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirtBar_coef
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_on
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Dop_opL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open WirtingerDerivatives
namespace Formalism.QuantumDeterminants
theorem _root_.solution : WeylFun := by
  intro m E _ _ l f hf
  have hr := reg_of_mem hf
  have h0 : ∀ x, x ∉ OmX m → f x = 0 := hf.2
  have hnot : ∀ x : Fin m → ℂ, x l = 0 → x ∉ OmX m := fun x h hx => hx l h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    simp only [cOp, ciOp, smul_smul]
    by_cases h : x l = 0
    · rw [h0 x (hnot x h), smul_zero]
    · rw [mul_inv_cancel₀ h, one_smul]
  · funext x
    simp only [cOp, ciOp, smul_smul]
    by_cases h : x l = 0
    · rw [h0 x (hnot x h), smul_zero]
    · rw [inv_mul_cancel₀ h, one_smul]
  · funext x
    by_cases hx : x ∈ OmX m
    · have e := Dop_opL hr hx l l 0 1
      have hw : wirt l (coef l 1) x = 1 := by
        rw [wirt_coef hx, if_pos ⟨by decide, rfl⟩]
        rfl
      change opL l 0 (opL l 1 f) x = _
      rw [opL_on l 0 _ hx]
      change x l • Dop l 0 (opL l 1 f) x = _
      rw [e]
      change x l • (wirt l (coef l 1) x • f x + x l • wirt l f x) = x l • pOp l f x + x l • f x
      simp only [pOp, hx, if_true, hw, one_smul]
      rw [smul_add, add_comm]
    · simp only [Pi.add_apply, pOp, cOp, hx, if_false, h0 x hx, smul_zero, add_zero]
  · funext x
    simp only [cbOp, cbiOp, smul_smul]
    by_cases h : x l = 0
    · rw [h0 x (hnot x h), smul_zero]
    · rw [mul_inv_cancel₀ (star_ne_zero.mpr h), one_smul]
  · funext x
    simp only [cbOp, cbiOp, smul_smul]
    by_cases h : x l = 0
    · rw [h0 x (hnot x h), smul_zero]
    · rw [inv_mul_cancel₀ (star_ne_zero.mpr h), one_smul]
  · funext x
    by_cases hx : x ∈ OmX m
    · have e := Dop_opL hr hx l l 3 4
      have hw : wirtBar l (coef l 4) x = 1 := by
        rw [wirtBar_coef hx, if_pos ⟨by decide, rfl⟩]
        rfl
      change opL l 3 (opL l 4 f) x = _
      rw [opL_on l 3 _ hx]
      change star (x l) • Dop l 3 (opL l 4 f) x = _
      rw [e]
      change star (x l) • (wirtBar l (coef l 4) x • f x + star (x l) • wirtBar l f x) =
        star (x l) • pbOp l f x + star (x l) • f x
      simp only [pbOp, hx, if_true, hw, one_smul]
      rw [smul_add, add_comm]
    · simp only [Pi.add_apply, pbOp, cbOp, hx, if_false, h0 x hx, smul_zero, add_zero]
end Formalism.QuantumDeterminants
