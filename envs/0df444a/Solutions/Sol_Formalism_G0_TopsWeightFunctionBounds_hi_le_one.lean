-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.hi_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:23.820239+00:00
-- url     : https://prove2.me/submissions/5f39f180-85d2-42ff-98f2-3332299a6b50

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
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : 1 / (2 - δ) ≤ 1 := by
  have h2 := two_sub_pos h1
  rw [div_le_one h2]; linarith
end Formalism.G0.TopsWeightFunctionBounds
