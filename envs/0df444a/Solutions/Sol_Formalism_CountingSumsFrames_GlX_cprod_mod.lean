-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.cprod_mod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:59.985272+00:00
-- url     : https://prove2.me/submissions/52f12d91-1723-4c22-b37d-cc8da1cb0384

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_cons
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
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.GlX
theorem _root_.solution {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) (cs : List ℤ) :
    G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v ∈ U := by
  induction cs with
  | nil => simp [GlW.cprod]
  | cons c cs ih =>
    rw [G.cprod_cons, List.map_cons, List.prod_cons]
    have hc := G.Cas_hwmod hU hv hr
    have e : G.Cas (G.cprod cs v) - ((c : ℤ) : K) • G.cprod cs v -
        ((((GlW.casI μ - c : ℤ)) : K) * (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod) • v =
      (G.Cas (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v) -
        ((c : ℤ) : K) • (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v)) +
        (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • (G.Cas v - ((GlW.casI μ : ℤ) : K) • v) := by
      rw [map_sub, map_smul]; push_cast; module
    rw [e]
    exact U.add_mem (U.sub_mem (G.Cas_mem hU ih) (U.smul_mem _ ih)) (U.smul_mem _ hc)
end Formalism.CountingSumsFrames.GlX
