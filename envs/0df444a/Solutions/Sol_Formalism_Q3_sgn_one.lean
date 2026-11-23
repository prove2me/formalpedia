-- Prove2me | solution 1 for Formalism.Q3.sgn_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:23.012124+00:00
-- url     : https://prove2.me/submissions/d4d68dbb-0611-4f1a-b4c4-c6eb65778103

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.Q3
open ZMod
namespace Formalism.Q3
theorem _root_.solution : sgn 1 = 1 := by
  unfold sgn; rw [if_pos rfl]
end Formalism.Q3
