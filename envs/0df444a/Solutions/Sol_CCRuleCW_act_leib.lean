-- Prove2me | solution 1 for CCRuleCW.act_leib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:50.915307+00:00
-- url     : https://prove2.me/submissions/62bb00a8-4e39-4753-99df-8d247d49a8fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_act_eq
import Theorems.Thm_CCRuleCW_curve_zero
import Theorems.Thm_CCRuleCW_curve_hasDerivAt
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
theorem _root_.solution (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (Q : B.Mat k r → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (H : B.Mat k r → E) (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    act o (fun x => Q x • H x) g = act o Q g • H g + Q g • act o H g := by
  obtain ⟨v, hv⟩ := exists_along H hH o hX g hg
  have h1 : HasFDerivAt Q (fderiv ℝ Q (curve o g 0)) (curve o g 0) :=
    ((hQ.differentiable (by norm_num)) _).hasFDerivAt
  have hQd := h1.comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt o g)
  rw [curve_zero] at hQd
  rw [act_eq, act_eq, act_eq, hv.deriv,
    show deriv (fun t => Q (curve o g t)) 0 = fderiv ℝ Q g (dir o g) from hQd.deriv]
  rw [show deriv (fun t => Q (curve o g t) • H (curve o g t)) 0 =
      (Q ∘ curve o g) 0 • v + fderiv ℝ Q g (dir o g) • H (curve o g 0) from (hQd.smul hv).deriv]
  simp only [Function.comp_apply, curve_zero]
  rw [add_comm]
end CCRuleCW
