-- Prove2me | solution 1 for CCRuleCW.good_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:51.419805+00:00
-- url     : https://prove2.me/submissions/d8ba4ed9-6e81-44de-8f8d-bc1ef5f72007

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_one_le_gN


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
theorem _root_.solution {a b : ℕ} (hab : a ≤ b) (Q : B.Mat k r → ℂ) (h : Good a Q) : Good b Q := by
  refine ⟨h.1, fun ops hl => ?_⟩
  obtain ⟨C, hC⟩ := h.2 ops hl
  refine ⟨max C 0, fun g hg => (hC g hg).trans ?_⟩
  have h1 := one_le_gN g hg
  calc C * B.gN g ^ a ≤ max C 0 * B.gN g ^ a :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
    _ ≤ max C 0 * B.gN g ^ b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hab) (le_max_right _ _)
end CCRuleCW
