-- Prove2me | solution 1 for CCRuleCW.act_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:49.792296+00:00
-- url     : https://prove2.me/submissions/0f31c8f8-ec5d-4299-98eb-76727377995e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_act_eq
import Theorems.Thm_CCRuleCW_exists_along

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
    (h₁ : B.CkOn (⊤ : ℕ∞) (B.GV k r) f₁) (h₂ : B.CkOn (⊤ : ℕ∞) (B.GV k r) f₂)
    (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    act o (fun x => f₁ x + f₂ x) g = act o f₁ g + act o f₂ g := by
  obtain ⟨v₁, hv₁⟩ := exists_along f₁ h₁ o hX g hg
  obtain ⟨v₂, hv₂⟩ := exists_along f₂ h₂ o hX g hg
  rw [act_eq, act_eq, act_eq, hv₁.deriv, hv₂.deriv]
  exact (hv₁.add hv₂).deriv
end CCRuleCW
