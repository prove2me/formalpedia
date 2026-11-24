-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.kappa_zero_tendsto_factorials
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:08.440432+00:00
-- url     : https://prove2.me/submissions/6d09b13f-e445-4209-a45a-86acff2cea0e

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_choose_lim
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
open MvPolynomial Finset Formalism.GM Filter Topology
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (o z e r : ℕ) :
    Tendsto (fun n : ℕ => kap0 o n z e r) atTop (𝓝 (((z + e).choose e : ℝ) * e.factorial * e.factorial)) := by
  have h1 := choose_lim (o + r) (1 + e) e
  have h2 := choose_lim (o + r + z) 1 e
  have hf : (1 / (e.factorial : ℝ)) ≠ 0 := by
    have : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero e
    simpa using this
  have h3 := ((h1.div h2 hf).const_mul (((z + e).choose e : ℝ) * e.factorial * e.factorial))
  rw [div_self hf, mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (e + 1)] with n hn
  have hn0 : (n : ℝ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
  unfold kap0
  rw [show o + n + r - 1 - e = n + (o + r) - (1 + e) by omega, show o + n + r + z - 1 = n + (o + r + z) - 1 by omega,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hc : (((n + (o + r + z) - 1).choose e : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  simp only [Pi.div_apply]
  push_cast
  field_simp
end Formalism.GM.leadingTermLemmas
