-- Prove2me | solution 1 for Formalism.G0.TailSumsP.latestDegrees_succ_some
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:21.751963+00:00
-- url     : https://prove2.me/submissions/03481874-5f08-41df-89a0-1b4c2deaee75

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
    {B : ℕ} (h : steps[i] = some B) :
    latestDegrees steps (i + 1) = B :: latestDegrees steps i := by
  unfold latestDegrees
  rw [List.take_add_one, List.getElem?_eq_getElem hi, h]
  simp
end Formalism.G0.TailSumsP
