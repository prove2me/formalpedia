-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.yangian_relation_three_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:39.316845+00:00
-- url     : https://prove2.me/submissions/a6e27f20-033f-4040-a8e7-5813c150dc4f

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_comm_of_inv
import Theorems.Thm_Formalism_YangianSpanCharacter_P_qdet_alg
import Theorems.Thm_Formalism_YangianSpanCharacter_P_diagonal_entry_eq_of_modular_relation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_key_mod

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
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.Y.Y3 := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hu1 hum hv hv1 huv
  rw [key_mod H hu hu1 hv hv1 huv]
  have hinvu := H.2.2.2.1 u hu
  have hinvm := H.2.2.2.1 (u - 1) hum
  have hml : mf t τinv u * lf t τinv u = τinv u * t u 0 0 - hf τinv q u := by
    rw [diagonal_entry_eq_of_modular_relation H hu hu1, ← mul_assoc, hinvu.2, one_mul]
    abel
  have qd : t u 0 0 - t u 1 0 * τinv u * t u 0 1 = q (u - 1) • τinv (u - 1) := by
    have hm := H.2.1 (u - 1)
    rw [sub_add_cancel] at hm
    have e1 : -(t u 1 0 * t (u - 1) 0 1) + t u 0 0 * t (u - 1) 1 1 = q (u - 1) • (1 : A) := by
      have h01 := congrFun (congrFun hm 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h01
    have e2 : -(t u 1 1 * t (u - 1) 0 1) + t u 0 1 * t (u - 1) 1 1 = 0 := by
      have h11 := congrFun (congrFun hm 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h11
    exact qdet_alg e1 e2 hinvu.2 hinvm.1
  have hc1 : t u 1 1 * τinv (u - 1) = τinv (u - 1) * t u 1 1 :=
    comm_of_inv hinvm.1 hinvm.2 (H.2.2.2.2.1 u (u - 1)).eq
  have hc2 : τinv (u - 1) * τinv u = τinv u * τinv (u - 1) :=
    comm_of_inv hinvu.1 hinvu.2 hc1.symm
  have hfm : hf τinv q (u - 1) = q (u - 1) • (τinv u * τinv (u - 1)) := by
    simp only [hf]; rw [sub_add_cancel, hc2]
  have hlm : lf t τinv u * mf t τinv u = τinv u * t u 0 0 - hf τinv q (u - 1) := by
    rw [hfm, ← mul_smul_comm, ← qd]
    simp only [lf, mf, mul_sub, mul_assoc]
    abel
  rw [hml, hlm]
  abel
end Formalism.YangianSpanCharacter.P
