-- Prove2me | solution 1 for CCRuleCW.mul_sum_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:20.928855+00:00
-- url     : https://prove2.me/submissions/d313f9d3-d6bf-4e9a-a3ca-25e69a56c7a7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg

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
namespace CCRuleCW
theorem _root_.solution {α : Type*} (l : List α) (c : ℝ) (f : α → ℝ) :
    c * (l.map f).sum = (l.map (fun p => c * f p)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]
end CCRuleCW
