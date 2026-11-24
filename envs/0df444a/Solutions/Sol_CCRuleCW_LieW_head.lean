-- Prove2me | solution 1 for CCRuleCW.LieW.head
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:54:03.063245+00:00
-- url     : https://prove2.me/submissions/95f47e62-5853-449f-8cae-0a5844488ffd

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
namespace LieW
theorem _root_.solution {o : Bool × B.Mat k r} {os : List (Bool × B.Mat k r)} (h : LieW (o :: os)) :
    B.inLie k r o.2 := h o (by simp)
end LieW
end CCRuleCW
