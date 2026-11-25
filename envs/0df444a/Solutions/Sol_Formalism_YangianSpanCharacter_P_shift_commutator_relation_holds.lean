-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.shift_commutator_relation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:51.459612+00:00
-- url     : https://prove2.me/submissions/fbd7eb5e-6c09-4f0a-8308-4d67738cf1a8

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_commutator_eq_eta_mul_sub

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
theorem _root_.solution : Formalism.YangianSpanCharacter.Y.Y2 := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hv huv
  exact commutator_eq_eta_mul_sub H hu hv huv
end Formalism.YangianSpanCharacter.P
