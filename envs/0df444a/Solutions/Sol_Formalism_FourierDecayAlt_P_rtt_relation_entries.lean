-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rtt_relation_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:43.121205+00:00
-- url     : https://prove2.me/submissions/096a2c1f-92ff-4761-a490-c66d7d7f1dcf

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
private theorem e1_mul_e2_apply {B : Type*} [Ring B] (X Y : Matrix (Fin 2) (Fin 2) B) (a b j l : Fin 2) :
    (Formalism.YangianSpanCharacter.T.E1 X * Formalism.YangianSpanCharacter.T.E2 Y) (a, b) (j, l) = X a j * Y b l := by
  fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.E1, Formalism.YangianSpanCharacter.T.E2]
private theorem e2_mul_e1_apply {B : Type*} [Ring B] (X Y : Matrix (Fin 2) (Fin 2) B) (a b j l : Fin 2) :
    (Formalism.YangianSpanCharacter.T.E2 Y * Formalism.YangianSpanCharacter.T.E1 X) (a, b) (j, l) = Y b l * X a j := by
  fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.E1, Formalism.YangianSpanCharacter.T.E2]
private theorem pf_mul_apply {B : Type*} [Ring B] (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B)
    (i k j l : Fin 2) : (Formalism.YangianSpanCharacter.T.Pf B * N) (i, k) (j, l) = N (k, i) (j, l) := by
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Pf]
private theorem mul_pf_apply {B : Type*} [Ring B] (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B)
    (i k j l : Fin 2) : (N * Formalism.YangianSpanCharacter.T.Pf B) (i, k) (j, l) = N (i, k) (l, j) := by
  fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Pf]
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : RTTEntries := by
  intro K B _ _ _ M v u hR i j k l
  have h := congrFun (congrFun hR (i, k)) (j, l)
  rw [mul_assoc, sub_mul, smul_mul_assoc, one_mul, Matrix.sub_apply, Matrix.smul_apply,
    e1_mul_e2_apply, pf_mul_apply, e1_mul_e2_apply] at h
  rw [mul_sub, mul_smul_comm, mul_one, Matrix.sub_apply, Matrix.smul_apply,
    e2_mul_e1_apply, mul_pf_apply, e2_mul_e1_apply] at h
  rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]
  exact h
end Formalism.FourierDecayAlt.P
