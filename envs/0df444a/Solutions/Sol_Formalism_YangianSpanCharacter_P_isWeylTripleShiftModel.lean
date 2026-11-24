-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.isWeylTripleShiftModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:04.579697+00:00
-- url     : https://prove2.me/submissions/fe2eae93-2469-4bcf-bbdb-a93d7a8049dc

import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeSymplecticShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.T.WeylModel := by
  refine ⟨?_, ?_, ?_⟩
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, LinearMap.funLeft_apply]
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, LinearMap.funLeft_apply]
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.pM, LinearMap.funLeft_apply]
    ring
end Formalism.YangianSpanCharacter.P
