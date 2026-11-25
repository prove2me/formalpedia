-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.minus_frame_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:29.247172+00:00
-- url     : https://prove2.me/submissions/1fa0cac4-bf0a-4f1b-8f08-378c2f74d925

import Definitions.Def_Formalism_YangianSpanCharacter_StatementF
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SymplecticTransposeEntryZeroOne
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_MinusFrameIdentity
import Theorems.Thm_Formalism_YangianSpanCharacter_P_qdet_mod
import Theorems.Thm_Formalism_YangianSpanCharacter_P_yangian_relation_three_holds
import Theorems.Thm_P2M_Formalism_YangianSpanCharacter_P_y1__mod_9fb34041d8dc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.YangianSpanCharacter.F
set_option linter.unusedSimpArgs false
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.F.MinusFrame := by
  intro 𝕜 A _ _ _ t τinv q S H Y Yb hY hY1 hYb hYb1 hYbm hd hd1 d tn τn Ln Gb
  have hd1' : d - 1 ≠ 0 := hd1
  have hne : Y ≠ Yb := fun h => hd (by rw [h, sub_self])
  have i0 := H.2.2.2.1 Y hY
  have hτl : t Y 1 1 * lf t τinv Y = t Y 1 0 := by
    unfold lf; rw [← mul_assoc, i0.1, one_mul]
  have hτm : t Y 1 1 * mf t τinv Y = t Y 0 1 := by
    unfold mf; rw [← mul_assoc, i0.1, one_mul]
  have QD : t Y 0 0 - t Y 0 1 * lf t τinv Y = q Y • τinv (Y + 1) := by
    have := qdet_mod H hY hY1; unfold lf; rw [← mul_assoc]; exact this
  have hτh : t Y 1 1 * hf τinv q Y = q Y • τinv (Y + 1) := by
    unfold hf; rw [mul_smul_comm, ← mul_assoc, i0.1, one_mul]
  have Y1' : t Y 1 1 * mf t τinv Yb - mf t τinv Yb * t Y 1 1 = t Y 1 1 * mu t τinv Y Yb :=
    y1'_mod H hY hYb hne
  have hμ0 : (Y - Yb) • mu t τinv Y Yb = mf t τinv Y - mf t τinv Yb := by
    unfold mu; exact smul_inv_smul₀ (sub_ne_zero.mpr hne) _
  have hτμ : d • (t Y 1 1 * mu t τinv Y Yb) = t Y 1 1 * mf t τinv Yb - t Y 0 1 := by
    show (Yb - Y) • (t Y 1 1 * mu t τinv Y Yb) = _
    rw [show Yb - Y = -(Y - Yb) by ring, neg_smul, ← mul_smul_comm, hμ0, mul_sub, hτm, neg_sub]
  have Y3 : (d - 1) • (mf t τinv Yb * lf t τinv Y - lf t τinv Y * mf t τinv Yb) =
      hf τinv q Y - hf τinv q (Yb - 1) :=
    yangian_relation_three_holds 𝕜 A t τinv q S H Yb Y hYb hYb1 hYbm hY hY1 (Ne.symm hne)
  have Y3' : mf t τinv Yb * lf t τinv Y - lf t τinv Y * mf t τinv Yb =
      (d - 1)⁻¹ • (hf τinv q Y - hf τinv q (Yb - 1)) := by
    rw [← Y3, inv_smul_smul₀ hd1']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, τn, blk, pt1, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, blk, pt1, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [τn, Ln, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hτl]
    rw [inv_smul_smul₀ hd1', hτh]
    linear_combination (norm := module) QD
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [τn, Gb, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) (-d) • Y1' - hτμ
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [Ln, Gb, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) Y3'
end Formalism.YangianSpanCharacter.P
