-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.rtt_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:09:22.300818+00:00
-- url     : https://prove2.me/submissions/3ede9d37-3592-43a5-80da-5227e46aa51a

import Definitions.Def_Formalism_YangianSpanCharacter_StatementB
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJReversed
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeSymplecticShift
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_RttRelation
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJTransposeReal
import Theorems.Thm_Formalism_QuantumDeterminants_weylRel_end
import Theorems.Thm_Formalism_YangianSpanCharacter_P_rttRelation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.QuantumDeterminants
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.B.RTTReal := by
  intro m E _ _ l Y Y'
  exact rttRelation ℂ (Module.End ℂ (WSm m E)) _ _ _ Y Y' (weylRel_end (E := E) l)
end Formalism.YangianSpanCharacter.P
