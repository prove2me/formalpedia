-- Prove2me | solution 1 for CCRuleCW.smooth_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:21:23.481136+00:00
-- url     : https://prove2.me/submissions/d34a1fd2-5b2b-41b9-9c83-32884734ae66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves

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
theorem _root_.solution (Q : B.Mat k r → E) (hQ : ContDiff ℝ ∞ Q) : B.CkOn (⊤ : ℕ∞) (B.GV k r) Q :=
  fun _ _ => ⟨Set.univ, Q, isOpen_univ, Set.mem_univ _, hQ.contDiffOn, fun _ _ _ => rfl⟩
end CCRuleCW
