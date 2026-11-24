-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.dsc_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:16.451811+00:00
-- url     : https://prove2.me/submissions/890070a8-a4f3-4856-9f16-b84c5ff52fb4

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Descent
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_applyWord_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_hw_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (k : ℕ)
    (y : MvPolynomial (Fin r × Fin n) ℤ_[p]) (hy : y ∈ weyl ℤ_[p] r n hn ν) :
    ∃ d ∈ weyl ℤ r n hn ν, ∃ z : MvPolynomial (Fin r × Fin n) ℤ_[p],
      y = map (Int.castRingHom ℤ_[p]) d + ((p : ℤ_[p]) ^ k) • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, 0, ?_⟩
    simp only [smul_zero, add_zero]
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, z1, rfl⟩ := hx
    obtain ⟨d2, hd2, z2, rfl⟩ := hy
    refine ⟨d1 + d2, Submodule.add_mem _ hd1 hd2, z1 + z2, ?_⟩
    rw [map_add, smul_add]; abel
  | smul a x _ hx =>
    obtain ⟨d, hd, z, rfl⟩ := hx
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
    have ha : a = ((PadicInt.appr a k : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ k * a' := by
      rw [← ha']; ring
    refine ⟨((PadicInt.appr a k : ℕ) : ℤ) • d, Submodule.smul_mem _ _ hd,
      a' • map (Int.castRingHom ℤ_[p]) d + a • z, ?_⟩
    have hm : map (Int.castRingHom ℤ_[p]) (((PadicInt.appr a k : ℕ) : ℤ) • d) =
        ((PadicInt.appr a k : ℕ) : ℤ_[p]) • map (Int.castRingHom ℤ_[p]) d := by
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]; simp
    have h1 : a • map (Int.castRingHom ℤ_[p]) d =
        ((PadicInt.appr a k : ℕ) : ℤ_[p]) • map (Int.castRingHom ℤ_[p]) d +
          ((p : ℤ_[p]) ^ k * a') • map (Int.castRingHom ℤ_[p]) d := by
      rw [← add_smul, ← ha]
    rw [hm, smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_comm a, h1, add_assoc]
end Formalism.InvariantFactorPaths.INST
