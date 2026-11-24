-- Prove2me | solution 1 for CCRuleCW.good_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:07:35.476474+00:00
-- url     : https://prove2.me/submissions/16df43bf-6d4b-4d06-9922-5753ae535ebc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_apO_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CCRuleCW
theorem _root_.solution (c : ℂ) : Good 0 (fun _ : B.Mat k r => c) := by
  refine ⟨contDiff_const, fun ops _ => ?_⟩
  obtain ⟨c', h1, h2⟩ := apO_const ops c
  exact ⟨‖c‖, fun g _ => by rw [h2, pow_zero, mul_one]; exact h1⟩
end CCRuleCW
