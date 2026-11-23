-- Prove2me | solution 1 for Formalism.G0.TailSumsP.latestDegrees_succ_none
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:46.104187+00:00
-- url     : https://prove2.me/submissions/2e122b49-9265-43ef-a903-b73eb2e5341a

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP
namespace Formalism.G0.TailSumsP
theorem _root_.solution (steps : List (Option ℕ)) (i : ℕ) (hi : i < steps.length)
    (h : steps[i] = none) :
    latestDegrees steps (i + 1) = latestDegrees steps i := by
  unfold latestDegrees
  rw [List.take_add_one, List.getElem?_eq_getElem hi, h]
  simp
end Formalism.G0.TailSumsP
