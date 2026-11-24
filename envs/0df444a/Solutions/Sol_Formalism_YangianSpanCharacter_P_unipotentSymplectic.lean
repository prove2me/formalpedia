-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.unipotentSymplectic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:13.253912+00:00
-- url     : https://prove2.me/submissions/b88b3c12-f93a-413c-9cd7-80e9170602f3

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
theorem _root_.solution : Formalism.YangianSpanCharacter.T.UJU := by
  intro R A _ _ _ s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
end Formalism.YangianSpanCharacter.P
