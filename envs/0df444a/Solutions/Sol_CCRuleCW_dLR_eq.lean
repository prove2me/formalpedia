-- Prove2me | solution 1 for CCRuleCW.dLR_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:51.922803+00:00
-- url     : https://prove2.me/submissions/ffa10a56-f253-4f1e-bacb-deae3092cd79

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_apO_append
import Theorems.Thm_CCRuleCW_apO_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution (u v : List (B.Mat k r)) (f : B.Mat k r → E) : B.dLR u v f = apO (opsW u v) f := by
  rw [opsW, apO_append, apO_R]
  induction u with
  | nil => rfl
  | cons x u ih =>
    rw [List.reverse_cons, List.map_append, apO_append, ← ih]
    rfl
end CCRuleCW
