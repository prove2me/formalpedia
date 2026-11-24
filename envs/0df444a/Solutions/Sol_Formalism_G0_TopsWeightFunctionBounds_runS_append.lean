-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.runS_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.65384+00:00
-- url     : https://prove2.me/submissions/3d56e35b-ad02-40e0-ab4b-57842348ff90

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
theorem _root_.solution (s : St) (l₁ l₂ : List Bool) :
    runS R L₂ s (l₁ ++ l₂) = runS R L₂ (runS R L₂ s l₁) l₂ := by
  simp [runS, List.foldl_append]
end Formalism.G0.TopsWeightFunctionBounds
