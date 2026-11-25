-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.plus_frame_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:42.194116+00:00
-- url     : https://prove2.me/submissions/86ab803d-d0b8-4849-9903-85b857c2f670

import Definitions.Def_Formalism_YangianSpanCharacter_StatementF
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SymplecticTransposeEntryZeroOne
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_MinusFrameIdentity
import Theorems.Thm_Formalism_YangianSpanCharacter_P_commutator_eq_eta_mul_sub
import Theorems.Thm_Formalism_YangianSpanCharacter_P_commutator_of_modular_relation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_smul_cancel


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
theorem _root_.solution : Formalism.YangianSpanCharacter.F.PlusFrame := by
  intro 𝕜 A _ _ _ t τinv q S H Y Ya hY hYa hD hD1 D tn l M N G Ginv
  have hD' : D ≠ 0 := hD
  have hne : Y ≠ Ya := sub_ne_zero.mp hD
  have hτl : t Y 1 1 * l = t Y 1 0 := by
    show t Y 1 1 * (τinv Y * t Y 1 0) = t Y 1 0
    rw [← mul_assoc, (H.2.2.2.1 Y hY).1, one_mul]
  have hη : D • eta t τinv Y Ya = l - lf t τinv Ya := by
    unfold eta; exact smul_inv_smul₀ hD _
  have Y1 : t Y 1 1 * lf t τinv Ya - lf t τinv Ya * t Y 1 1 = -(t Y 1 1 * eta t τinv Y Ya) :=
    commutator_of_modular_relation H hY hYa hne
  have Y2 : l * lf t τinv Ya - lf t τinv Ya * l = eta t τinv Y Ya * l - eta t τinv Y Ya * lf t τinv Ya :=
    by rw [commutator_eq_eta_mul_sub H hY hYa hne, mul_sub]
  have hτη : D • (t Y 1 1 * eta t τinv Y Ya) = t Y 1 1 * l - t Y 1 1 * lf t τinv Ya := by
    rw [← mul_smul_comm, hη, mul_sub]
  have f1 : D • (l * eta t τinv Y Ya) = l * l - l * lf t τinv Ya := by
    rw [← mul_smul_comm, hη, mul_sub]
  have f2 : D • (lf t τinv Ya * eta t τinv Y Ya) = lf t τinv Ya * l - lf t τinv Ya * lf t τinv Ya := by
    rw [← mul_smul_comm, hη, mul_sub]
  have f3 : D • (eta t τinv Y Ya * l) = l * l - lf t τinv Ya * l := by
    rw [← smul_mul_assoc, hη, sub_mul]
  have f4 : D • (eta t τinv Y Ya * lf t τinv Ya) = l * lf t τinv Ya - lf t τinv Ya * lf t τinv Ya := by
    rw [← smul_mul_assoc, hη, sub_mul]
  have hDD : D * D⁻¹ = 1 := mul_inv_cancel₀ hD'
  have hηe : eta t τinv Y Ya = D⁻¹ • (l - lf t τinv Ya) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, M, blk, sc, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hτl]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, N, blk, sc, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hτl]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;> simp [G, Ginv]
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [G, M, sc, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) (-D) • Y1 + hτη
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [N, M, Ginv, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    · linear_combination (norm := module) hη
    · rw [smul_smul, inv_mul_cancel₀ hD', one_smul]
    · apply smul_cancel hD'
      linear_combination (norm := module) (-1 : 𝕜) • f1 - (D - 1) • f2 - ((D - 1) * D) • Y2 -
        (D - 1) • f3 + (D - 1) • f4
    · rw [hηe]
      linear_combination (norm := module) -(hDD • l)
end Formalism.YangianSpanCharacter.P
