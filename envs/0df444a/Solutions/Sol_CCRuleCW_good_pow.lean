-- Prove2me | solution 1 for CCRuleCW.good_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:45.211415+00:00
-- url     : https://prove2.me/submissions/803a299d-e9c6-446a-95fc-e94b1f0429af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_good_congr
import Theorems.Thm_CCRuleCW_good_mul
import Theorems.Thm_CCRuleCW_good_const

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
theorem _root_.solution (Q : B.Mat k r → ℂ) (h : Good 1 Q) : ∀ m : ℕ, Good m (fun g => Q g ^ m)
  | 0 => good_congr (fun g => (pow_zero (Q g)).symm) (good_const 1)
  | m + 1 => good_congr (fun g => (pow_succ (Q g) m).symm) (good_mul _ _ (solution Q h m) h)
end CCRuleCW
