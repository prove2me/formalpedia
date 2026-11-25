-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.twisted_j_transpose_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:31.020164+00:00
-- url     : https://prove2.me/submissions/e9bab9b0-2ae3-4e2d-86c5-4244acbde3a2

import Definitions.Def_Formalism_YangianSpanCharacter_StatementB
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJReversed
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeSymplecticShift
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_RttRelation
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJTransposeReal
import Theorems.Thm_Formalism_QuantumDeterminants_weylRel_end_bar
import Theorems.Thm_Formalism_YangianSpanCharacter_P_transpose_j_reversed


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
theorem _root_.solution : Formalism.YangianSpanCharacter.B.TvJTsReal := by
  intro m E _ _ l Y
  obtain ⟨h1, h2, h3⟩ := weylRel_end_bar (E := E) l
  have h3' : cbEnd (E := E) l * -pbEnd l = -pbEnd l * cbEnd l + cbEnd l := by
    rw [mul_neg, neg_mul, h3]; abel
  exact transpose_j_reversed ℂ (Module.End ℂ (WSm m E)) _ _ _ Y h1 h2 h3'
end Formalism.YangianSpanCharacter.P
