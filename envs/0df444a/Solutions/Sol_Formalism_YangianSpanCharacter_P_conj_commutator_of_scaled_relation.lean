-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.conj_commutator_of_scaled_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:16.99635+00:00
-- url     : https://prove2.me/submissions/6a86215a-3dbe-4775-90d6-18f7ca1463a6

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_comm_of_inv

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
theorem _root_.solution {a b ai bi x y : A} {c : 𝕜} (hc : c ≠ 0)
    (hR : c • (a * y - y * a) = a * y - b * x) (hb1 : b * bi = 1) (hb2 : bi * b = 1)
    (ha1 : a * ai = 1) (hab : a * b = b * a) :
    a * (bi * y) - bi * y * a = -(a * (c⁻¹ • (ai * x - bi * y))) := by
  have hc' : a * bi = bi * a := comm_of_inv hb1 hb2 hab
  have hc'' : a * (bi * y) = bi * (a * y) := by rw [← mul_assoc, hc', mul_assoc]
  have hay : a * y - y * a = c⁻¹ • (a * y - b * x) := by
    rw [← hR, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hbx : bi * (b * x) = x := by rw [← mul_assoc, hb2, one_mul]
  have hax : a * (ai * x) = x := by rw [← mul_assoc, ha1, one_mul]
  calc a * (bi * y) - bi * y * a = bi * (a * y - y * a) := by
        rw [hc'', mul_sub, mul_assoc]
    _ = c⁻¹ • (bi * (a * y) - x) := by
        rw [hay, mul_smul_comm, mul_sub, hbx]
    _ = -(a * (c⁻¹ • (ai * x - bi * y))) := by
        rw [mul_smul_comm, mul_sub, hax, hc'', ← smul_neg, neg_sub]
end Formalism.YangianSpanCharacter.P
