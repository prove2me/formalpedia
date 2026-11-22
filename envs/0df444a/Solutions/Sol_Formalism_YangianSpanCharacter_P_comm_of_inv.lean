-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.comm_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:44:39.77767+00:00
-- url     : https://prove2.me/submissions/c1688b53-f515-4849-82fb-0af9de39d058

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
theorem _root_.solution {a b bi : A} (h1 : b * bi = 1) (h2 : bi * b = 1) (hab : a * b = b * a) :
    a * bi = bi * a := by
  calc a * bi = (bi * b) * (a * bi) := by rw [h2, one_mul]
    _ = bi * (a * b) * bi := by rw [hab]; simp only [mul_assoc]
    _ = bi * a := by simp only [mul_assoc]; rw [h1, mul_one]
end Formalism.YangianSpanCharacter.P
