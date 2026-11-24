-- Prove2me | solution 1 for CCRuleCW.ruleC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:14:03.938884+00:00
-- url     : https://prove2.me/submissions/b818aed9-33c3-49fd-bf9d-26535ec704c6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_good_congr
import Theorems.Thm_CCRuleCW_good_poly
import Theorems.Thm_CCRuleCW_main


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
theorem _root_.solution : C2.RuleC := by
  intro k r E _ _ A F D P hF hP
  obtain ⟨q, hq, hPq⟩ := hP
  exact main A D P (good_congr (fun g => (hPq g).symm) (good_poly q D hq)) F hF
end CCRuleCW
