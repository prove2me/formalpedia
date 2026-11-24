-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.l_shift_from_determinant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:06.269335+00:00
-- url     : https://prove2.me/submissions/8431f631-82bf-4d32-b6a0-b12712b48f8e

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
namespace Formalism.FourierDecayAlt.P
private theorem mul_J_mul_transpose_apply' {A : Type*} [Ring A] (M N : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (M * Formalism.YangianSpanCharacter.T.J A * Nᵀ) i j = M i 0 * N j 1 - M i 1 * N j 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] <;> first | abel | noncomm_ring
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : LShift := by
  intro 𝕜 A _ _ _ t τinv q S h Y hY hY1
  obtain ⟨-, -, h3, h4, -, -⟩ := h
  have e := congrFun (congrFun (h3 Y) 1) 1
  have e0 : (q Y • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0 := by simp [Formalism.YangianSpanCharacter.T.J]
  rw [mul_J_mul_transpose_apply', e0, sub_eq_zero] at e
  unfold lf
  calc τinv Y * t Y 1 0 = τinv Y * t Y 1 0 * (t (Y + 1) 1 1 * τinv (Y + 1)) := by
        rw [(h4 (Y + 1) hY1).1, mul_one]
    _ = τinv Y * (t Y 1 0 * t (Y + 1) 1 1) * τinv (Y + 1) := by simp only [mul_assoc]
    _ = τinv Y * (t Y 1 1 * t (Y + 1) 1 0) * τinv (Y + 1) := by rw [e]
    _ = τinv Y * t Y 1 1 * t (Y + 1) 1 0 * τinv (Y + 1) := by simp only [mul_assoc]
    _ = t (Y + 1) 1 0 * τinv (Y + 1) := by rw [(h4 Y hY).2, one_mul]
end Formalism.FourierDecayAlt.P
