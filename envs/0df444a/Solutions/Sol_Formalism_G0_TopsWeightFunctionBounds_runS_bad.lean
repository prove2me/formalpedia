-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.runS_bad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.714599+00:00
-- url     : https://prove2.me/submissions/6a1e2922-24c2-4e52-a157-956ed0e75860

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_runS_cons

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
theorem _root_.solution (bs : List Bool) : runS R L₂ .bad bs = .bad := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [runS_cons]
    have : step R L₂ .bad b = .bad := by cases b <;> rfl
    rw [this, ih]
end Formalism.G0.TopsWeightFunctionBounds
