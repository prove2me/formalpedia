-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.qdet_mod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:58.931955+00:00
-- url     : https://prove2.me/submissions/aa33edb6-edba-478b-b431-d067d841e912

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_qdet_alg

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
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution (H : ModHyp t τinv q S) {Y : 𝕜} (hY : Y ∈ S) (hY1 : Y + 1 ∈ S) :
    t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0 = q Y • τinv (Y + 1) := by
  have hm := H.2.2.1 Y
  have e1 : -(t Y 0 1 * t (Y + 1) 1 0) + t Y 0 0 * t (Y + 1) 1 1 = q Y • (1 : A) := by
    have h01 := congrFun (congrFun hm 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h01
  have e2 : -(t Y 1 1 * t (Y + 1) 1 0) + t Y 1 0 * t (Y + 1) 1 1 = 0 := by
    have h11 := congrFun (congrFun hm 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h11
  exact qdet_alg e1 e2 (H.2.2.2.1 Y hY).2 (H.2.2.2.1 (Y + 1) hY1).1
end Formalism.YangianSpanCharacter.P
