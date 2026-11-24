-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.rht_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:57.638524+00:00
-- url     : https://prove2.me/submissions/a11ff080-af80-448c-bf5d-fd67cc1d7d55

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_sum_eU_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (b : S) (d : ℂ) (T : M2 (SlopeTestRemainingChoices S A)) (j : Fin 2) :
    (Rht0 b d * T : M2 (SlopeTestRemainingChoices S A)) 1 j =
      ins b ((d - 1)⁻¹ • !![d • T 1 j, 0; -T 0 j, (d - 1) • T 1 j]) := by
  have h := Wd1.sum_eU_diag (A := A) b
  rw [Fin.sum_univ_two] at h
  have e : T 1 j = eU b 0 0 * T 1 j + eU b 1 1 * T 1 j := by rw [← add_mul, h, one_mul]
  have l : (Rht0 b d * T : M2 (SlopeTestRemainingChoices S A)) 1 j =
      (d - 1)⁻¹ • (d • T 1 j - (eU b 1 0 * T 0 j + eU b 1 1 * T 1 j)) := by
    unfold Rht0
    rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul,
      Matrix.one_mul, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Q0, Matrix.of_apply]
  rw [l]
  unfold ins
  simp only [Matrix.smul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_smul_comm, mul_zero, smul_zero, add_zero, mul_neg]
  rw [← smul_add, ← smul_add]
  congr 1
  rw [sub_smul, one_smul]
  have e' : d • T 1 j = d • (eU b 0 0 * T 1 j) + d • (eU b 1 1 * T 1 j) := by rw [← smul_add, ← e]
  rw [e']
  abel
end Formalism.FourierDecayAlt.P.Fr9
