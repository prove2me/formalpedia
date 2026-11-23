-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.edge_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:59.061218+00:00
-- url     : https://prove2.me/submissions/cd05f92c-fa27-4b0a-9c68-4cf8eb03309b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_ratio_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_a_sub_u_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_kDel_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_card_mid

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
theorem _root_.solution (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') :
    ∏ i ∈ Icc 2 (c.k - 1), ((c.a - c.u de i) / (c.a - c.u de' i)) ≤ Real.exp (1 / 3) := by
  have hkD := kDel_pos c hc
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  refine (prod_ratio_le (Icc 2 (c.k - 1)) (fun i => c.a - c.u de i) (fun i => c.a - c.u de' i)
    (1 / (4 * c.k)) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)).trans ?_
  · have := a_sub_u_pos c de' hc hw' i hi; linarith
  · have := a_sub_u_pos c de hc hw i hi; linarith
  · have h1 := a_sub_u_pos c de' hc hw' i hi
    have h2 := (abs_le.mp (u_mid_diff c de de' hc hw hw' i hi)).1
    have h3 : c.Del ≤ 1 / (4 * c.k) * (c.a - c.u de' i) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      linarith
    linarith
  · apply Real.exp_le_exp.mpr
    rw [card_mid c hc, mul_one_div, div_le_iff₀ (by positivity)]
    linarith
end Formalism.FourierDecayAlt.P.Sz4
