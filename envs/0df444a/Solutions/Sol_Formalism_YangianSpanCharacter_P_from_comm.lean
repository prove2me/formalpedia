-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.from_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:42.750985+00:00
-- url     : https://prove2.me/submissions/e1bdac24-4623-4e63-949d-90770c407607

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
theorem _root_.solution {a l e : A} (h : a * l - l * a = -(a * e)) : l * a = a * (l + e) := by
  rw [mul_add]
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel
end Formalism.YangianSpanCharacter.P
