-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.WF_init
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:43.857073+00:00
-- url     : https://prove2.me/submissions/b8b68f86-806f-4871-9936-a45e50a2c446

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
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {R : ℕ} (hR : 1 ≤ R) (K : ℕ) (ev : Bool) : WF R (init K ev) := by
  unfold init
  split_ifs
  · exact True.intro
  · show 0 < R; omega
end Formalism.G0.TopsWeightFunctionBounds
