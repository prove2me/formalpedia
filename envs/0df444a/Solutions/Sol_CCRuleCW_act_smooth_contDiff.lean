-- Prove2me | solution 1 for CCRuleCW.act_smooth_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:40:45.933637+00:00
-- url     : https://prove2.me/submissions/3b56c3c2-a665-4464-841c-e94d6b74ec88

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_dir_contDiff
import Theorems.Thm_CCRuleCW_act_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate Nat ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution (Q : B.Mat k r → E) (hQ : ContDiff ℝ ∞ Q) (o : Bool × B.Mat k r) :
    ContDiff ℝ ∞ (act o Q) := by
  rw [act_smooth Q hQ o]
  exact (hQ.fderiv_right (by simp)).clm_apply (dir_contDiff o)
end CCRuleCW
