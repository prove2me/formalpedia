-- Prove2me | solution 1 for CCRuleCW.opsW_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:21.889405+00:00
-- url     : https://prove2.me/submissions/ed2bfe0a-c105-4391-96a7-b29bfce51456

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_apO_nil
import Theorems.Thm_CCRuleCW_apO_cons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CCRuleCW.apO_nil
attribute [local simp] CCRuleCW.apO_cons

set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution (u v : List (B.Mat k r)) : (opsW u v).length = u.length + v.length := by
  simp [opsW, Nat.add_comm]
end CCRuleCW
