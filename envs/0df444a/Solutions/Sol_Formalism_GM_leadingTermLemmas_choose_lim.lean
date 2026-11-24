-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.choose_lim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:34.378365+00:00
-- url     : https://prove2.me/submissions/3b19c99c-631e-481f-8cbb-73bf57eafae1

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_tendsto_lin
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
theorem _root_.solution (c s j : ℕ) :
    Tendsto (fun n : ℕ => ((n + c - s).choose j : ℝ) / (n : ℝ) ^ j) atTop (𝓝 (1 / (j.factorial : ℝ))) := by
  have hprod : Tendsto (fun n : ℕ => ∏ i ∈ range j, (((n : ℝ) + ((c : ℝ) - s - i)) / n)) atTop (𝓝 1) := by
    have := tendsto_finsetProd (range j) (fun i _ => tendsto_lin ((c : ℝ) - s - i))
    simpa using this
  have h2 := hprod.div_const (j.factorial : ℝ)
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (s + j + 1)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hd := Nat.descFactorial_eq_factorial_mul_choose (n + c - s) j
  rw [Nat.descFactorial_eq_prod_range] at hd
  have hcast : ((∏ i ∈ range j, (n + c - s - i) : ℕ) : ℝ) = ∏ i ∈ range j, ((n : ℝ) + ((c : ℝ) - s - i)) := by
    push_cast
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' : i < j := Finset.mem_range.mp hi
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hC : ((n + c - s).choose j : ℝ) = (∏ i ∈ range j, ((n : ℝ) + ((c : ℝ) - s - i))) / j.factorial := by
    rw [← hcast, hd]; push_cast; field_simp
  rw [hC, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  field_simp
end Formalism.GM.leadingTermLemmas
