-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.adjoint_l_shift_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:53.388809+00:00
-- url     : https://prove2.me/submissions/3fee60af-427d-4220-966f-10ff94b85285

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
theorem _root_.solution : AdjL := by
  intro 𝕜 A _ _ _ _ t τinv q S RR h hRR Y hY hY1 hst
  obtain ⟨-, h2, -, h4, -, -⟩ := h
  have H := congrFun (congrFun (h2 Y) 1) 1
  have c11 : (q Y • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0 := by simp [Formalism.YangianSpanCharacter.T.J]
  rw [transpose_mul_J_mul_apply, c11, sub_eq_zero] at H
  have hm : mf t τinv (Y + 1) = t Y 0 1 * τinv Y := by
    unfold mf
    calc τinv (Y + 1) * t (Y + 1) 0 1 = τinv (Y + 1) * (t (Y + 1) 0 1 * t Y 1 1) * τinv Y := by
          rw [mul_assoc (τinv (Y + 1)), mul_assoc, (h4 Y hY).1, mul_one]
      _ = t Y 0 1 * τinv Y := by
          rw [H, ← mul_assoc, (h4 (Y + 1) hY1).2, one_mul]
  have s11 : star (t Y 1 1) * RR = RR * t Y 1 1 := by
    have := hst 1 1
    rwa [star_mul, hRR] at this
  have s10 : star (t Y 1 0) * RR = RR * t Y 0 1 := by
    have := hst 1 0
    rwa [star_mul, hRR] at this
  have sτ : star (τinv Y) * RR = RR * τinv Y := by
    calc star (τinv Y) * RR = star (τinv Y) * (RR * t Y 1 1) * τinv Y := by
          rw [mul_assoc (star (τinv Y)), mul_assoc RR, (h4 Y hY).1, mul_one]
      _ = star (t Y 1 1 * τinv Y) * RR * τinv Y := by
          rw [← s11, star_mul]
          noncomm_ring
      _ = RR * τinv Y := by rw [(h4 Y hY).1, star_one, one_mul]
  rw [hm]
  unfold lf
  rw [star_mul, mul_assoc, sτ, ← mul_assoc (star (t Y 1 0)), s10, mul_assoc]
end Formalism.FourierDecayAlt.P
