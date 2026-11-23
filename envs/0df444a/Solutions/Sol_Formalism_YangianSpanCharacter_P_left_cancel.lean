-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.left_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:43.300711+00:00
-- url     : https://prove2.me/submissions/700916c0-c203-493e-abb5-27740a900c1a

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation

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
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution {b bi x y : A} (h2 : bi * b = 1) (h : b * x = b * y) : x = y := by
  calc x = bi * b * x := by rw [h2, one_mul]
    _ = bi * (b * y) := by rw [mul_assoc, h]
    _ = y := by rw [← mul_assoc, h2, one_mul]
end Formalism.YangianSpanCharacter.P
