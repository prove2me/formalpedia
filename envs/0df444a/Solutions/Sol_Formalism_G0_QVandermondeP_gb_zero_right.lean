-- Prove2me | solution 1 for Formalism.G0.QVandermondeP.gb_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:27.556998+00:00
-- url     : https://prove2.me/submissions/fcf9c7bf-4c3d-42f2-b90a-f55fde1b8067

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.QVandermondeP
namespace Formalism.G0.QVandermondeP
theorem _root_.solution (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl
end Formalism.G0.QVandermondeP
