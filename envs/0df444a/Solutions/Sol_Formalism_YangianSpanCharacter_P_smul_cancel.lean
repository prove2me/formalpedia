-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:20.423628+00:00
-- url     : https://prove2.me/submissions/75123b68-f4da-4349-9038-58290595689d

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
theorem _root_.solution {c : 𝕜} (hc : c ≠ 0) {x y : A} (h : c • x = c • y) : x = y := by
  calc x = c⁻¹ • c • x := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • c • y := by rw [h]
    _ = y := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
end Formalism.YangianSpanCharacter.P
