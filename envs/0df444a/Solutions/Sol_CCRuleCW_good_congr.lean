-- Prove2me | solution 1 for CCRuleCW.good_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:40:57.402967+00:00
-- url     : https://prove2.me/submissions/0ab1cc39-312d-48bc-9e6e-19f6adf94063

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd

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
theorem _root_.solution {D : ℕ} {Q₁ Q₂ : B.Mat k r → ℂ} (h : ∀ g, Q₁ g = Q₂ g) (h₁ : Good D Q₁) : Good D Q₂ := by
  have : Q₁ = Q₂ := funext h
  exact this ▸ h₁
end CCRuleCW
