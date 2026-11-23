-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:35.342799+00:00
-- url     : https://prove2.me/submissions/9262f31d-1c3b-4a21-94da-051813b2f1c7

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_two_sub_pos

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
theorem _root_.solution (h1 : δ ≤ 1) : 0 ≤ (1 - δ) / (2 - δ) := by
  have h2 := two_sub_pos h1
  exact div_nonneg (by linarith) h2.le
end Formalism.G0.TopsWeightFunctionBounds
