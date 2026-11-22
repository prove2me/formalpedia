-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.runS_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:11.619062+00:00
-- url     : https://prove2.me/submissions/dca8acd4-6639-4140-99bc-54fda8d1e4fb

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
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (s : St) (b : Bool) (bs : List Bool) :
    runS R L₂ s (b :: bs) = runS R L₂ (step R L₂ s b) bs := rfl
end Formalism.G0.TopsWeightFunctionBounds
