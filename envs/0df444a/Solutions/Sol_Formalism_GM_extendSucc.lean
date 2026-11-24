-- Prove2me | solution 1 for Formalism.GM.extendSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:01.48058+00:00
-- url     : https://prove2.me/submissions/be258234-03b0-4a3f-9b7f-3af3c9aabd68

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
namespace Formalism.GM
theorem _root_.solution : M.FreezeStep := by
  intro p _ N r LL ρ n hn f
  unfold M.freeze
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_comm hn]
end Formalism.GM
