-- Prove2me | solution 1 for CCRuleCW.exists_along
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:19.890106+00:00
-- url     : https://prove2.me/submissions/24b24b59-b3d9-4a94-bcba-8131d7165a9d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_along

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
theorem _root_.solution (H : B.Mat k r → E) (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    ∃ v, HasDerivAt (fun t => H (curve o g t)) v 0 := by
  obtain ⟨U, f', hU, hgU, hf', hagree⟩ := hH g hg
  exact ⟨_, along H hU hf' hagree o hX g hgU hg⟩
end CCRuleCW
