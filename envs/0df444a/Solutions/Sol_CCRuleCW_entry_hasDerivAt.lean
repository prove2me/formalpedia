-- Prove2me | solution 1 for CCRuleCW.entry_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:28.3707+00:00
-- url     : https://prove2.me/submissions/89a741a6-1ba9-428a-be1a-0e2e9d1aa8e3

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
set_option backward.isDefEq.respectTransparency false
namespace CCRuleCW
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have e1 : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) =
      fun t : ℝ => Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp (t • X)) := by
    funext t
    have : (t : ℂ) • X = t • X := by ext a b; simp [Complex.real_smul]
    rw [this]; rfl
  have e2 : X i j = Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp ((0 : ℝ) • X) * X) := by
    simp [NormedSpace.exp_zero]
  rw [e1, e2]
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
end CCRuleCW
