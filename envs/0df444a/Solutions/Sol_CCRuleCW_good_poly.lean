-- Prove2me | solution 1 for CCRuleCW.good_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:52:57.954118+00:00
-- url     : https://prove2.me/submissions/b3fc5355-edc4-4d72-b1d9-72ee4a8c52bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_good_mono
import Theorems.Thm_CCRuleCW_good_add
import Theorems.Thm_CCRuleCW_good_mul
import Theorems.Thm_CCRuleCW_good_const
import Theorems.Thm_CCRuleCW_good_mono_prod
import Theorems.Thm_CCRuleCW_apO_cons
import Theorems.Thm_CCRuleCW_apO_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CCRuleCW.apO_cons
attribute [local simp] CCRuleCW.apO_nil



set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CCRuleCW
theorem _root_.solution (q : MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ)
    (D : ℕ) (hq : q.totalDegree ≤ D) :
    Good D (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) := by
  have e : (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) =
      ∑ d ∈ q.support, fun g : B.Mat k r => q.coeff d * ∏ i ∈ d.support, xv g i ^ d i := by
    funext g
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ (Good D) (fun a b ha hb => good_add a b ha hb)
    (good_mono (Nat.zero_le D) _ (good_const 0)) ?_
  intro d hd
  have hdeg : (∑ i ∈ d.support, d i) ≤ D := (MvPolynomial.le_totalDegree hd).trans hq
  exact good_mono (by simpa using hdeg) _ (good_mul _ _ (good_const (q.coeff d)) (good_mono_prod d d.support))
end CCRuleCW
