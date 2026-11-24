-- Prove2me | solution 1 for CCRuleCW.apO_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:40:59.250392+00:00
-- url     : https://prove2.me/submissions/64ddfe51-9b59-426c-a7b5-c2bd1ea38d0f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_act_eq
import Theorems.Thm_CCRuleCW_apO_cons
import Theorems.Thm_CCRuleCW_apO_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CCRuleCW.apO_cons
attribute [local simp] CCRuleCW.apO_nil



set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CCRuleCW
theorem _root_.solution : ∀ (ops : List (Bool × B.Mat k r)) (c : ℂ),
    ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ apO ops (fun _ : B.Mat k r => c) = fun _ => c'
  | [], c => ⟨c, le_rfl, rfl⟩
  | o :: os, c => by
    have h0 : act o (fun _ : B.Mat k r => c) = fun _ => (0 : ℂ) := by
      funext g
      rw [act_eq]
      simp
    obtain ⟨c', h1, h2⟩ := solution os 0
    refine ⟨c', h1.trans (by simp), ?_⟩
    simp only [apO_cons, h0, h2]
end CCRuleCW
