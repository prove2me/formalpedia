-- Prove2me | solution 1 for CCRuleCW.apO_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:39:31.928886+00:00
-- url     : https://prove2.me/submissions/89078481-b85a-41f9-b22f-26de85cfdf83

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_act_eq
import Theorems.Thm_CCRuleCW_apO_cons
import Theorems.Thm_CCRuleCW_apO_nil
import Theorems.Thm_CCRuleCW_curve_hasDerivAt
import Theorems.Thm_CCRuleCW_curve_zero
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
theorem _root_.solution : ∀ (ops : List (Bool × B.Mat k r)) (ℓ : B.Mat k r →L[ℝ] ℂ),
    ∃ ℓ' : B.Mat k r →L[ℝ] ℂ, apO ops ⇑ℓ = ⇑ℓ'
  | [], ℓ => ⟨ℓ, rfl⟩
  | o :: os, ℓ => by
    have h : act o ⇑ℓ = ⇑(ℓ.comp (dirL o)) := by
      funext g
      rw [act_eq]
      exact (ℓ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (curve_hasDerivAt o g) (curve_zero o g).symm).deriv
    obtain ⟨ℓ', h'⟩ := solution os (ℓ.comp (dirL o))
    exact ⟨ℓ', by simp only [apO_cons, h, h']⟩
end CCRuleCW
