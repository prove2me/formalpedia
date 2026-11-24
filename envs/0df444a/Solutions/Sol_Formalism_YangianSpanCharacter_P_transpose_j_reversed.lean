-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.transpose_j_reversed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:11.857405+00:00
-- url     : https://prove2.me/submissions/be27f09d-e81e-471c-b944-9a69c6f35a9c

import Definitions.Def_Formalism_YangianSpanCharacter_TJTrev
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJReversed

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
theorem _root_.solution : Formalism.YangianSpanCharacter.T.TJTrev := by
  intro R A _ _ _ q d di Y h1 h2 h3
  have hc : algebraMap R A Y * d = d * algebraMap R A Y := Algebra.commutes Y d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add, add_mul, mul_add]
  all_goals first
    | exact h1
    | exact h2
    | (rw [h3, hc]; abel)
end Formalism.YangianSpanCharacter.P
