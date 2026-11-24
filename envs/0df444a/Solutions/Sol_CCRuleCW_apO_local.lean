-- Prove2me | solution 1 for CCRuleCW.apO_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:19.045872+00:00
-- url     : https://prove2.me/submissions/5b97948b-9b97-4423-9e1f-998e38994bce

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_LieW_head
import Theorems.Thm_CCRuleCW_LieW_tail
import Theorems.Thm_CCRuleCW_act_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution : ∀ (ops : List (Bool × B.Mat k r)), LieW ops → ∀ f₁ f₂ : B.Mat k r → E,
    (∀ g ∈ B.GV k r, f₁ g = f₂ g) → ∀ g ∈ B.GV k r, apO ops f₁ g = apO ops f₂ g
  | [], _, _, _, h, g, hg => h g hg
  | o :: os, hl, f₁, f₂, h, g, hg =>
      solution os hl.tail _ _ (fun g' hg' => act_local o hl.head f₁ f₂ h g' hg') g hg
end CCRuleCW
