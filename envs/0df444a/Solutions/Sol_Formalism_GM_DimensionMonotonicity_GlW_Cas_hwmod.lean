-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.Cas_hwmod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:33.443873+00:00
-- url     : https://prove2.me/submissions/054f9b96-5236-4892-be18-9fc7ae441604

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_diag_of_isWt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_apply
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity_GlW_comm__671fb396e97c
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) : G.Cas v - ((casI μ : ℤ) : K) • v ∈ U := by
  have hmem : ∀ a b, G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v ∈ U := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [if_neg h.ne, if_pos h, G.comm' a b b a v, if_pos rfl, if_pos rfl,
        G.E_diag_of_isWt hv a, G.E_diag_of_isWt hv b]
      have hm : G.E b a (G.E a b v) ∈ U := hU b a _ (hr a b h)
      convert hm using 1
      push_cast
      rw [sub_smul]
      abel
    · subst h
      rw [if_pos rfl, G.E_diag_of_isWt hv a, map_smul, G.E_diag_of_isWt hv a, smul_smul]
      simp
    · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), Int.cast_zero, zero_smul, sub_zero]
      exact hU a b _ (hr b a h)
  have hsum : G.Cas v - ((casI μ : ℤ) : K) • v = ∑ a, ∑ b, (G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v) := by
    rw [Cas_apply, casI, Int.cast_sum, Finset.sum_smul]
    simp only [Int.cast_sum, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hmem a b
end Formalism.GM.DimensionMonotonicity.GlW
