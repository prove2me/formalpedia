-- Prove2me | solution 1 for CCRuleCW.norm_sum_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:56:36.659045+00:00
-- url     : https://prove2.me/submissions/6b11fce2-aac1-4ac6-9a9f-bcabc87a1a41

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
theorem _root_.solution {α F : Type*} [SeminormedAddCommGroup F] (l : List α) (f : α → F) :
    ‖(l.map f).sum‖ ≤ (l.map (fun p => ‖f p‖)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)
end CCRuleCW
