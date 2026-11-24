-- Prove2me | solution 1 for CCRuleCW.good_mono_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:36:31.628782+00:00
-- url     : https://prove2.me/submissions/116f4bfb-16e5-4fec-9607-0d35e5ded408

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_good_congr
import Theorems.Thm_CCRuleCW_good_mul
import Theorems.Thm_CCRuleCW_good_const
import Theorems.Thm_CCRuleCW_good_var
import Theorems.Thm_CCRuleCW_good_pow
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
theorem _root_.solution (d : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℕ)
    (s : Finset ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)))) :
    Good (∑ i ∈ s, d i) (fun g : B.Mat k r => ∏ i ∈ s, xv g i ^ d i) := by
  induction s using Finset.induction_on with
  | empty => simpa using good_const (k := k) (r := r) 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact good_congr (fun g => by rw [Finset.prod_insert ha])
      (good_mul _ _ (good_pow _ (good_var a) (d a)) ih)
end CCRuleCW
