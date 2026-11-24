-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.aF_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:43.848665+00:00
-- url     : https://prove2.me/submissions/35c38b55-597c-44b5-b756-2be0c7b5a64b

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (h0 : 0 ≤ δ) : aF L₂ δ ≤ 1 / 2 := by
  unfold aF
  have : (0 : ℝ) ≤ L₂ * δ := mul_nonneg (Nat.cast_nonneg _) h0
  nlinarith
end Formalism.G0.TopsWeightFunctionBounds
