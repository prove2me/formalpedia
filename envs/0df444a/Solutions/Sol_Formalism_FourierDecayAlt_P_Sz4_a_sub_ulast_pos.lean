-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.a_sub_ulast_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:18.599584+00:00
-- url     : https://prove2.me/submissions/8e52cb23-f0f6-4773-b459-1125266e456f

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_v_one_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_kDel_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_bp_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (c : Cfg) (hc : c.Ok) : 0 < c.a - c.ulast := by
  have h1 := kDel_pos c hc
  have h2 := v_one_nonneg c hc
  have h3 := hc.ha
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  unfold Cfg.ulast
  by_cases ht : c.top = true
  · have := bp_pos c hc ht
    simp only [ht, if_true]; linarith
  · have hv : c.v 1 = c.vlast + 4 * c.Del * ((c.k : ℝ) - 2) := by unfold Cfg.v; push_cast; ring
    have m : 0 ≤ c.Del * ((c.k : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
    simp only [ht]; simp only [Bool.false_eq_true, if_false]; linarith
end Formalism.FourierDecayAlt.P.Sz4
