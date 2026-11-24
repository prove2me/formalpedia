-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.coeff_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:32.389025+00:00
-- url     : https://prove2.me/submissions/fc6d93b7-a9b2-47f6-88f9-3b8523a2e6a6

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
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
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open Filter Topology Finset
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (R : Polynomial ℝ) (D : ℕ) (L : ℝ)
    (h : Tendsto (fun n : ℕ => R.eval (n : ℝ) / (n : ℝ) ^ D) atTop (𝓝 L)) : R.coeff D = L := by
  set Q : Polynomial ℝ := Polynomial.X ^ D with hQ
  have hQe : ∀ x : ℝ, Q.eval x = x ^ D := fun x => by simp [hQ]
  have hQd : Q.degree = D := by simp [hQ]
  have hQl : Q.leadingCoeff = 1 := by simp [hQ]
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  rcases lt_trichotomy R.degree Q.degree with hlt | heq | hgt
  · have h0 := (Polynomial.div_tendsto_atTop_zero_of_degree_lt R Q hlt).comp hnat
    simp only [Function.comp_def, hQe] at h0
    have hL := tendsto_nhds_unique h h0
    rw [hL]
    exact Polynomial.coeff_eq_zero_of_degree_lt (by rw [← hQd]; exact hlt)
  · have h0 := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq R Q heq).comp hnat
    simp only [Function.comp_def, hQe, hQl, div_one] at h0
    have hL := tendsto_nhds_unique h h0
    rw [hL, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some (heq.trans hQd)]
  · exfalso
    have hR0 : R ≠ 0 := fun h0 => by rw [h0, Polynomial.degree_zero] at hgt; exact absurd hgt (by simp)
    have hlc : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR0
    rcases lt_or_gt_of_ne hlc with hneg | hpos
    · have h0 := (Polynomial.div_tendsto_atBot_of_degree_gt' R Q hgt (by rw [hQl, div_one]; exact hneg)).comp hnat
      simp only [Function.comp_def, hQe] at h0
      exact not_tendsto_nhds_of_tendsto_atBot h0 L h
    · have h0 := (Polynomial.div_tendsto_atTop_of_degree_gt' R Q hgt (by rw [hQl, div_one]; exact hpos)).comp hnat
      simp only [Function.comp_def, hQe] at h0
      exact not_tendsto_nhds_of_tendsto_atTop h0 L h
end Formalism.GM.leadingTermLemmas
