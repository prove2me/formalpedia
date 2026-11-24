-- Prove2me | solution 1 for CCRuleCW.act_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:18:26.309852+00:00
-- url     : https://prove2.me/submissions/fd696c72-daf9-409e-8adb-c59c25b0f0e0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_act_eq
import Theorems.Thm_CCRuleCW_curve_zero
import Theorems.Thm_CCRuleCW_curve_hasDerivAt

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
    act o Q = fun g => fderiv ℝ Q g (dir o g) := by
  funext g
  rw [act_eq]
  have h1 : HasFDerivAt Q (fderiv ℝ Q (curve o g 0)) (curve o g 0) :=
    ((hQ.differentiable (by norm_num)) _).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt o g)
  rw [curve_zero] at h2
  exact h2.deriv
end CCRuleCW
