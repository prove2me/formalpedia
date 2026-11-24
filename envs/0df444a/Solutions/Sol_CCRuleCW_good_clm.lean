-- Prove2me | solution 1 for CCRuleCW.good_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:01:58.44643+00:00
-- url     : https://prove2.me/submissions/1df03789-19f1-413a-b728-ea909d82416a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_apO_clm
import Theorems.Thm_CCRuleCW_sup_le_gN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CCRuleCW
theorem _root_.solution (ℓ : B.Mat k r →L[ℝ] ℂ) : Good 1 ⇑ℓ := by
  refine ⟨ℓ.contDiff, fun ops _ => ?_⟩
  obtain ⟨ℓ', h⟩ := apO_clm ops ℓ
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x : B.Mat k r, ‖ℓ' x‖ ≤ M * ‖x‖ := by
    exact ℓ'.bound
  refine ⟨M, fun g _ => ?_⟩
  rw [h, pow_one]
  exact (hM g).trans (mul_le_mul_of_nonneg_left (sup_le_gN g) hM0.le)
end CCRuleCW
