-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.wedgeMapInLieAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:13.919913+00:00
-- url     : https://prove2.me/submissions/f7ee0b88-6d17-42fe-b806-7e90b78b254c

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_commutator_of_modular_relation

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
theorem _root_.solution : Formalism.YangianSpanCharacter.Y.Y1 := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hv huv
  exact commutator_of_modular_relation H hu hv huv
end Formalism.YangianSpanCharacter.P
