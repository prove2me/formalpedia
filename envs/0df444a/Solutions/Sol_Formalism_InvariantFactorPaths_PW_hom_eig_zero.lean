-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.hom_eig_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:44.016802+00:00
-- url     : https://prove2.me/submissions/e607122c-a98f-46f7-a568-bc395daade95

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_Ecc
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_comp
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
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_apply
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



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity
variable {K V V₁ V₂ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution [CharZero K] (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ)
    (hW : G₂.Stable W) (hb : WtBound2 G₁ G₂ W l) (z : Fin n) (k : ℤ) (φ : V₁ →ₗ[K] V₂) (hφ : ∀ x, φ x ∈ W)
    (he : homAct G₁.E G₂.E z z φ = (k : K) • φ) (hk : (l : ℤ) < |k|) : φ = 0 := by
  have key : ∀ μ x, φ (G₁.comp μ x) = 0 := by
    intro μ x
    by_contra hy
    have hx' : G₁.comp μ x ≠ 0 := fun h => hy (by rw [h, map_zero])
    have hE : G₂.E z z (φ (G₁.comp μ x)) = ((k + μ z : ℤ) : K) • φ (G₁.comp μ x) := by
      have h := congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ (G₁.comp μ x)) he
      simp only [homAct_apply, LinearMap.smul_apply] at h
      rw [G₁.diag, map_smul] at h
      rw [Int.cast_add, add_smul, ← h]
      abel
    have hc : ∀ ν, G₂.comp ν (φ (G₁.comp μ x)) = 0 := by
      intro ν
      by_contra hν
      have e1 := G₂.comp_Ecc ν z (φ (G₁.comp μ x))
      rw [hE, map_smul] at e1
      have e2 : (((k + μ z : ℤ) : K) - ((ν z : ℤ) : K)) • G₂.comp ν (φ (G₁.comp μ x)) = 0 := by
        rw [sub_smul, e1, sub_self]
      rcases smul_eq_zero.mp e2 with h | h
      · have h3 : k + μ z = ν z := by exact_mod_cast sub_eq_zero.mp h
        have h4 := hb μ ν (G₁.comp μ x) _ hx' hν (G₂.graded_of hW ν _ (hφ _)) (G₁.isWt_comp μ x)
          (G₂.isWt_comp ν _) z
        rw [← h3, add_sub_cancel_right] at h4
        omega
      · exact hν h
    apply hy
    have h := G₂.sum_comp (φ (G₁.comp μ x)) ∅ (fun ν _ => hc ν)
    simpa using h.symm
  ext x
  obtain ⟨S, hS⟩ := G₁.dec x
  rw [← G₁.sum_comp x S hS, map_sum, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun μ _ => key μ x
end Formalism.InvariantFactorPaths.PW
