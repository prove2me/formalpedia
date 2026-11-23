-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.top_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:48.039561+00:00
-- url     : https://prove2.me/submissions/967c5fe3-99f7-4a57-a72d-dda2488d3b15

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_ratio_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_card_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_bp_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid_nonneg

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
theorem _root_.solution (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (ht : c.top = true)
    (hw : IsWord c.k de) (hw' : IsWord c.k de') :
    ∏ i ∈ Icc 2 (c.k - 1), ((c.u de i + c.bp) / (c.u de' i + c.bp)) ≤ Real.exp (c.vthp / 3) := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  have hb := bp_pos c hc ht
  refine (prod_ratio_le (Icc 2 (c.k - 1)) (fun i => c.u de i + c.bp) (fun i => c.u de' i + c.bp)
    (c.Del / c.bp) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)).trans ?_
  · have := u_mid_nonneg c de' hc hw' i hi; linarith
  · have := u_mid_nonneg c de hc hw i hi; linarith
  · have h1 := u_mid_nonneg c de' hc hw' i hi
    have h2 := (abs_le.mp (u_mid_diff c de de' hc hw hw' i hi)).2
    have h3 : c.Del ≤ c.Del / c.bp * (c.u de' i + c.bp) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hb]
      nlinarith
    linarith
  · apply Real.exp_le_exp.mpr
    rw [card_mid c hc]
    have e : c.vthp = 4 * c.k * c.Del / c.bp := by simp [Cfg.vthp, ht]
    rw [e, div_div, mul_div_assoc', div_le_div_iff₀ hb (by positivity)]
    nlinarith [mul_pos hb (by linarith : (0 : ℝ) < c.Del), mul_pos (mul_pos hb (by linarith : (0 : ℝ) < c.Del)) (by linarith : (0 : ℝ) < c.k)]
end Formalism.FourierDecayAlt.P.Sz4
