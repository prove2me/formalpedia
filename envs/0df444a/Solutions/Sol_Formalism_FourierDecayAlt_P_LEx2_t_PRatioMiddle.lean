-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_PRatioMiddle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:36:32.245349+00:00
-- url     : https://prove2.me/submissions/fa069e9f-8a19-45cb-9680-f40223b588ee

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : PRatioMiddle := by
  intro n lam α β L Y s hαβ hR hL hnL hs h1 h2 h3 h4
  have hI : 0 < β - α := by linarith
  rw [Finset.abs_prod, Finset.abs_prod]
  have hx0 : 0 ≤ 3 * L / (β - α) := by positivity
  have hfac : ∀ t, |Y + lam t| ≤ (1 + 3 * L / (β - α)) * |Y + s + lam t| := by
    intro t
    have hdist : (β - α) / 3 ≤ |Y + s + lam t| := by
      by_contra hc
      push_neg at hc
      apply hR t
      rw [abs_lt] at hc
      constructor <;> linarith [hc.1, hc.2]
    have h5 : |Y + lam t| ≤ |Y + s + lam t| + |s| := by
      rcases abs_cases (Y + lam t) with h | h <;> rcases abs_cases (Y + s + lam t) with h' | h' <;>
        rcases abs_cases s with h'' | h'' <;> linarith [h.1, h'.1, h''.1]
    have h3L : L ≤ 3 * L / (β - α) * |Y + s + lam t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI]; nlinarith
    nlinarith
  calc ∏ t, |Y + lam t| ≤ ∏ t, (1 + 3 * L / (β - α)) * |Y + s + lam t| :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun t _ => hfac t)
    _ = (1 + 3 * L / (β - α)) ^ n * ∏ t, |Y + s + lam t| := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ Real.exp 3 * ∏ t, |Y + s + lam t| := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        have h6 : 1 + 3 * L / (β - α) ≤ Real.exp (3 * L / (β - α)) := by
          linarith [Real.add_one_le_exp (3 * L / (β - α))]
        calc (1 + 3 * L / (β - α)) ^ n ≤ (Real.exp (3 * L / (β - α))) ^ n :=
              pow_le_pow_left₀ (by positivity) h6 n
          _ = Real.exp (n * (3 * L / (β - α))) := by rw [Real.exp_nat_mul]
          _ ≤ Real.exp 3 := by
              apply Real.exp_le_exp.mpr
              rw [mul_div_assoc', div_le_iff₀ hI]; nlinarith
end Formalism.FourierDecayAlt.P.LEx2
