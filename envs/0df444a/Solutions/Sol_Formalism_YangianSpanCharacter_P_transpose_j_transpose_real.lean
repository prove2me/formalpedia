-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.transpose_j_transpose_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:43:57.367107+00:00
-- url     : https://prove2.me/submissions/a4020504-799b-4982-ae9c-4858ffe4f368

import Definitions.Def_Formalism_YangianSpanCharacter_StatementB
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJReversed
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeSymplecticShift
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_RttRelation
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJTransposeReal
import Theorems.Thm_Formalism_QuantumDeterminants_weylRel_end
import Theorems.Thm_Formalism_YangianSpanCharacter_P_transposeSymplecticShift


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
theorem _root_.solution : Formalism.YangianSpanCharacter.B.TJTReal := by
  intro m E _ _ l Y
  exact transposeSymplecticShift ℂ (Module.End ℂ (WSm m E)) _ _ _ Y (weylRel_end (E := E) l)
end Formalism.YangianSpanCharacter.P
