-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.yangian_relation_first_alt_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:20:19.192473+00:00
-- url     : https://prove2.me/submissions/4eac0186-21d3-4bcc-9733-60918bd763f2

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_P2M_Formalism_YangianSpanCharacter_P_y1__mod_9fb34041d8dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.Y.Y1' := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hv huv
  exact y1'_mod H hu hv huv
end Formalism.YangianSpanCharacter.P
