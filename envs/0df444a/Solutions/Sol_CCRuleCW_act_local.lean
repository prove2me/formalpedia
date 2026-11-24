-- Prove2me | solution 1 for CCRuleCW.act_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:01:57.719143+00:00
-- url     : https://prove2.me/submissions/b91f15bd-1989-47c7-97c5-05f648a429db

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_act_eq
import Theorems.Thm_CCRuleCW_curve_mem

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
theorem _root_.solution (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (f₁ f₂ : B.Mat k r → E)
    (h : ∀ g ∈ B.GV k r, f₁ g = f₂ g) (g : B.Mat k r) (hg : g ∈ B.GV k r) : act o f₁ g = act o f₂ g := by
  rw [act_eq, act_eq]
  congr 1
  funext t
  exact h _ (curve_mem o g t hX hg)
end CCRuleCW
