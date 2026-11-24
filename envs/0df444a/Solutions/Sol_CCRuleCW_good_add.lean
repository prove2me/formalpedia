-- Prove2me | solution 1 for CCRuleCW.good_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:40:10.987228+00:00
-- url     : https://prove2.me/submissions/d3cb248e-d5c7-4899-be26-52c79f991b8d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_apO_add
import Theorems.Thm_CCRuleCW_smooth_ck


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
theorem _root_.solution {D : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good D Q₁) (h₂ : Good D Q₂) :
    Good D (fun g => Q₁ g + Q₂ g) := by
  refine ⟨h₁.1.add h₂.1, fun ops hl => ?_⟩
  obtain ⟨C₁, hC₁⟩ := h₁.2 ops hl
  obtain ⟨C₂, hC₂⟩ := h₂.2 ops hl
  refine ⟨C₁ + C₂, fun g hg => ?_⟩
  rw [apO_add ops hl Q₁ Q₂ (smooth_ck Q₁ h₁.1) (smooth_ck Q₂ h₂.1) g hg]
  have e1 := hC₁ g hg
  have e2 := hC₂ g hg
  calc _ ≤ ‖apO ops Q₁ g‖ + ‖apO ops Q₂ g‖ := norm_add_le _ _
    _ ≤ C₁ * B.gN g ^ D + C₂ * B.gN g ^ D := add_le_add e1 e2
    _ = (C₁ + C₂) * B.gN g ^ D := by ring
end CCRuleCW
