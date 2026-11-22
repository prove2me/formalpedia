-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.aF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:16.608802+00:00
-- url     : https://prove2.me/submissions/6f1ee021-040b-48ab-9acc-c14612d8ea00

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
theorem _root_.solution (hLδ : (L₂ : ℝ) * δ ≤ 1) : 0 ≤ aF L₂ δ := by
  unfold aF; nlinarith
end Formalism.G0.TopsWeightFunctionBounds
