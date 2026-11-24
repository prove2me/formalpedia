-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.homInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:23:46.709225+00:00
-- url     : https://prove2.me/submissions/d7b5fbda-1d35-41ef-b1b8-299e5cc4c0a8

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_glRel_of
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hom_eig_zero
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
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hom_relation_holds
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
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (h1 : InvInv) : HomInv := by
  intro K V₁ V₂ _ _ _ _ _ _ n G₁ G₂ W l hW hb φ hφ h0
  have hrel : GlRel (homAct G₁.E G₂.E) := hom_relation_holds K V₁ V₂ (Fin n) G₁.E G₂.E (glRel_of G₁) (glRel_of G₂)
  obtain ⟨c1, c2, c3⟩ := h1 K (V₁ →ₗ[K] V₂) (Fin n) (homAct G₁.E G₂.E) hrel l (mapsInto V₁ W)
    (fun a b ψ hψ x => by
      rw [homAct_apply]
      exact W.sub_mem (hW a b _ (hψ x)) (hψ _))
    (fun z k ψ hψ he hk => hom_eig_zero G₁ G₂ W l hW hb z k ψ hψ he hk)
    (List.finRange n) (List.nodup_finRange n) φ hφ (fun a _ => h0 a)
  refine ⟨fun a b x => ?_, c2, c3⟩
  have h := congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ x) (c1 a (List.mem_finRange a) b (List.mem_finRange b))
  simp only [homAct_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.mp h).symm
end Formalism.InvariantFactorPaths.PW
