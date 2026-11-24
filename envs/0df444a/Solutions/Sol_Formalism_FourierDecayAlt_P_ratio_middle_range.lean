-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ratio_middle_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:26:00.20756+00:00
-- url     : https://prove2.me/submissions/08bfebf3-19cb-4984-96a2-663451a056d7

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.PRatioMiddle := by
  intro n lam α β L Y s hαβ hroot hL hnL hs hY1 hY2 hYs1 hYs2
  set D := (β - α) / 3 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hfac : ∀ t, D ≤ |Y + s + lam t| := by
    intro t
    have ht := hroot t
    by_cases h : -lam t ≤ α
    · rw [abs_of_pos (by linarith)]
      linarith
    · push_neg at h
      have hb : β ≤ -lam t := by
        by_contra hc
        push_neg at hc
        exact ht ⟨h, hc⟩
      rw [abs_of_neg (by linarith)]
      linarith
  have hrat : ∀ t, |Y + lam t| ≤ (1 + L / D) * |Y + s + lam t| := by
    intro t
    have h1 := abs_sub_abs_le_abs_sub (Y + lam t) (Y + s + lam t)
    have h1' : (Y + lam t) - (Y + s + lam t) = -s := by ring
    rw [h1', abs_neg] at h1
    have h2 : L ≤ L / D * |Y + s + lam t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hD0]
      exact mul_le_mul_of_nonneg_left (hfac t) hL
    nlinarith
  have hprod : |∏ t, (Y + lam t)| ≤ (1 + L / D) ^ n * |∏ t, (Y + s + lam t)| := by
    rw [Finset.abs_prod, Finset.abs_prod]
    calc ∏ t, |Y + lam t| ≤ ∏ t, ((1 + L / D) * |Y + s + lam t|) :=
          Finset.prod_le_prod (fun t _ => abs_nonneg _) (fun t _ => hrat t)
      _ = (1 + L / D) ^ n * ∏ t, |Y + s + lam t| := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hx : 1 + L / D ≤ Real.exp (L / D) := by linarith [Real.add_one_le_exp (L / D)]
  have hexp : (1 + L / D) ^ n ≤ Real.exp 3 := by
    calc (1 + L / D) ^ n ≤ (Real.exp (L / D)) ^ n := by gcongr <;> exact hx
      _ = Real.exp (n * (L / D)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 3 := by
          apply Real.exp_le_exp.mpr
          have he : (n:ℝ) * (L / D) = (n * L) / D := by ring
          rw [he, div_le_iff₀ hD0]
          linarith
  calc |∏ t, (Y + lam t)| ≤ (1 + L / D) ^ n * |∏ t, (Y + s + lam t)| := hprod
    _ ≤ Real.exp 3 * |∏ t, (Y + s + lam t)| := mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
end Formalism.FourierDecayAlt.P
