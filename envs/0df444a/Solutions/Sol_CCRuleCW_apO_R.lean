-- Prove2me | solution 1 for CCRuleCW.apO_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:00:01.742714+00:00
-- url     : https://prove2.me/submissions/1621826d-4876-4b34-949a-a5c5c0d750ff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_apO_append

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
theorem _root_.solution (v : List (B.Mat k r)) (f : B.Mat k r → E) :
    apO (v.reverse.map (fun X => (false, X))) f = B.Rw v f := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    rw [List.reverse_cons, List.map_append, apO_append, ih]
    rfl
end CCRuleCW
