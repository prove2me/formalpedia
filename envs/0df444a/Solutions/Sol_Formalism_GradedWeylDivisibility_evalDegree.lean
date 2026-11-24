-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.evalDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:17.848171+00:00
-- url     : https://prove2.me/submissions/1af788f1-a141-42ed-960a-43237a14bf0f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCdegLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_EvalDeg
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcdeg_degreeOf_X_le
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcdeg_degreeOf_aeval_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : EvalDeg := by
  intro B _ τ _ x y c _ _ _ p
  apply lcdeg_degreeOf_aeval_le
  intro m hm
  have hf : ∀ v, degreeOf c ((fun v : τ => if v = x then (1 : MvPolynomial τ B)
      else if v = y then -X c else X v) v) ≤ (if v = y then 1 else 0) + (if v = c then 1 else 0) := by
    intro v
    by_cases hvx : v = x
    · subst hvx
      simp only [if_true]
      have h1 : degreeOf c (1 : MvPolynomial τ B) = 0 := by rw [← C_1, degreeOf_C]
      rw [h1]
      exact Nat.zero_le _
    · by_cases hvy : v = y
      · subst hvy
        simp only [hvx, if_false, if_true, degreeOf_neg]
        have h2 := lcdeg_degreeOf_X_le (R := B) c c
        simp only [if_true] at h2
        omega
      · simp only [hvx, hvy, if_false, zero_add]
        exact lcdeg_degreeOf_X_le (R := B) c v
  refine le_trans (Finset.sum_le_sum (g := fun v => m v * (if v = y then 1 else 0) +
    m v * (if v = c then 1 else 0)) fun v _ => ?_) ?_
  · rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (hf v)
  · rw [Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hy := monomial_le_degreeOf y hm
    have hc := monomial_le_degreeOf c hm
    split_ifs <;> omega
end Formalism.GradedWeylDivisibility
