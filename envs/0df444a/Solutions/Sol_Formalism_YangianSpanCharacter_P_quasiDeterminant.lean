-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.quasiDeterminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:47.155279+00:00
-- url     : https://prove2.me/submissions/d0be2cb6-38df-430d-b25b-71a3d3ab2049

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SymplecticTransposeEntryZeroOne
import Theorems.Thm_Formalism_YangianSpanCharacter_P_symplectic_transpose_entry_zero_one
import Theorems.Thm_Formalism_YangianSpanCharacter_P_symplectic_transpose_entry_one_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.Y
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.Y.QuasiDet := by
  unfold Formalism.YangianSpanCharacter.Y.QuasiDet
  intro 𝕜 A _ _ _ t τinv q S hL Y hY hY1
  unfold Formalism.YangianSpanCharacter.Y.ModHyp at hL
  obtain ⟨-, -, h3, h4, -, -⟩ := hL
  have e2 := symplectic_transpose_entry_zero_one h3 Y
  have e3 := symplectic_transpose_entry_one_one h3 Y
  obtain ⟨a1, -⟩ := h4 (Y + 1) hY1
  obtain ⟨-, b2⟩ := h4 Y hY
  have key : t (Y + 1) 1 0 = τinv Y * t Y 1 0 * t (Y + 1) 1 1 := by
    calc t (Y + 1) 1 0 = τinv Y * t Y 1 1 * t (Y + 1) 1 0 := by rw [b2, one_mul]
      _ = τinv Y * (t Y 1 1 * t (Y + 1) 1 0) := mul_assoc _ _ _
      _ = τinv Y * (t Y 1 0 * t (Y + 1) 1 1) := by rw [e3]
      _ = τinv Y * t Y 1 0 * t (Y + 1) 1 1 := (mul_assoc _ _ _).symm
  have e4 : (t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0) * t (Y + 1) 1 1 = q Y • (1 : A) := by
    rw [← e2, key]
    noncomm_ring
  calc t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0
        = (t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0) * (t (Y + 1) 1 1 * τinv (Y + 1)) := by
          rw [a1, mul_one]
    _ = (t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0) * t (Y + 1) 1 1 * τinv (Y + 1) :=
          (mul_assoc _ _ _).symm
    _ = q Y • τinv (Y + 1) := by rw [e4, smul_mul_assoc, one_mul]
end Formalism.YangianSpanCharacter.P
