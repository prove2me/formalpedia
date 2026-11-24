-- Prove2me | solution 1 for CCRuleCW.apO_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:22:14.182887+00:00
-- url     : https://prove2.me/submissions/e48b7f61-7edf-4832-8c20-a81d67db08dd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_apO_nil
import Theorems.Thm_CCRuleCW_apO_cons
import Theorems.Thm_CCRuleCW_LieW_head
import Theorems.Thm_CCRuleCW_LieW_tail
import Theorems.Thm_CCRuleCW_apO_local
import Theorems.Thm_CCRuleCW_act_add
import Theorems.Thm_CCRuleCW_act_ck

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CCRuleCW.apO_nil
attribute [local simp] CCRuleCW.apO_cons

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
    B.CkOn (⊤ : ℕ∞) (B.GV k r) f₁ → B.CkOn (⊤ : ℕ∞) (B.GV k r) f₂ →
    ∀ g ∈ B.GV k r, apO ops (fun x => f₁ x + f₂ x) g = apO ops f₁ g + apO ops f₂ g
  | [], _, _, _, _, _, _, _ => rfl
  | o :: os, hl, f₁, f₂, h₁, h₂, g, hg => by
      simp only [apO_cons]
      rw [apO_local os hl.tail (act o (fun x => f₁ x + f₂ x)) (fun x => act o f₁ x + act o f₂ x)
        (fun g' hg' => act_add o hl.head f₁ f₂ h₁ h₂ g' hg') g hg]
      exact solution os hl.tail _ _ (act_ck f₁ h₁ o hl.head) (act_ck f₂ h₂ o hl.head) g hg
end CCRuleCW
