-- Prove2me | solution 1 for Formalism.G0.TailSumsP.cnt_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:32.869896+00:00
-- url     : https://prove2.me/submissions/3e99742a-4223-47cc-844e-cb7f23118b63

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
theorem _root_.solution (steps : List (Option ℕ)) (i : ℕ) : cnt steps i i = 0 := by
  simp [cnt]
end Formalism.G0.TailSumsP
