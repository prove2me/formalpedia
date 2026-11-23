-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.qdet_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:43.608813+00:00
-- url     : https://prove2.me/submissions/c42ec068-aee6-4565-9467-9c63133df696

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
theorem _root_.solution {x00 x01 x10 τ τi τ' τ'i z : A} {k : 𝕜}
    (e1 : -(x01 * z) + x00 * τ' = k • 1) (e2 : -(τ * z) + x10 * τ' = 0)
    (h2 : τi * τ = 1) (h3 : τ' * τ'i = 1) : x00 - x01 * τi * x10 = k • τ'i := by
  have hτz : τ * z = x10 * τ' := neg_add_eq_zero.mp e2
  have hz : z = τi * (x10 * τ') := by rw [← hτz, ← mul_assoc, h2, one_mul]
  have h4 : (x00 - x01 * τi * x10) * τ' = k • (1 : A) := by
    rw [← e1, hz, sub_mul]
    simp only [mul_assoc]
    abel
  calc x00 - x01 * τi * x10 = (x00 - x01 * τi * x10) * τ' * τ'i := by
        rw [mul_assoc _ τ' τ'i, h3, mul_one]
    _ = k • τ'i := by rw [h4, smul_mul_assoc, one_mul]
end Formalism.YangianSpanCharacter.P
