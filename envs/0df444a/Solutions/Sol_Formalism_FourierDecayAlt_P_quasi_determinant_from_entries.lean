-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.quasi_determinant_from_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:07.741505+00:00
-- url     : https://prove2.me/submissions/aaeb0e27-27f7-4198-8c85-6b1d05cf8ea5

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
private theorem transpose_mul_J_mul_apply {A : Type*} [Ring A] (M N : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (Mᵀ * Formalism.YangianSpanCharacter.T.J A * N) i j = M 0 i * N 1 j - M 1 i * N 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] <;> first | abel | noncomm_ring
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : QuasiDetT := by
  intro 𝕜 A _ _ _ t τinv q S h Y hY hY1
  obtain ⟨-, h2, -, h4, -, -⟩ := h
  have H := h2 (Y - 1)
  rw [sub_add_cancel] at H
  have e01 := congrFun (congrFun H 0) 1
  have e11 := congrFun (congrFun H 1) 1
  have c01 : (q (Y - 1) • Formalism.YangianSpanCharacter.T.J A) 0 1 = q (Y - 1) • (1 : A) := by simp [Formalism.YangianSpanCharacter.T.J]
  have c11 : (q (Y - 1) • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0 := by simp [Formalism.YangianSpanCharacter.T.J]
  rw [transpose_mul_J_mul_apply, c01] at e01
  rw [transpose_mul_J_mul_apply, c11, sub_eq_zero] at e11
  have hs : t (Y - 1) 0 1 = τinv Y * t Y 0 1 * t (Y - 1) 1 1 := by
    rw [mul_assoc, e11, ← mul_assoc, (h4 Y hY).2, one_mul]
  have key : (t Y 0 0 - t Y 1 0 * τinv Y * t Y 0 1) * t (Y - 1) 1 1 = q (Y - 1) • (1 : A) := by
    rw [← e01, hs]
    noncomm_ring
  calc t Y 0 0 - t Y 1 0 * τinv Y * t Y 0 1
      = (t Y 0 0 - t Y 1 0 * τinv Y * t Y 0 1) * t (Y - 1) 1 1 * τinv (Y - 1) := by
        rw [mul_assoc _ (t (Y - 1) 1 1), (h4 (Y - 1) hY1).1, mul_one]
    _ = q (Y - 1) • τinv (Y - 1) := by rw [key, smul_mul_assoc, one_mul]
end Formalism.FourierDecayAlt.P
