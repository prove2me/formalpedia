-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.Rht0_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:52.2224+00:00
-- url     : https://prove2.me/submissions/735b697a-4ee0-45c6-b510-8ddfd1793ec8

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_apply_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_smul_cancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (b : S) (d : K) (hd : d ≠ 1) (X : M2 (SlopeTestRemainingChoices S A)) (hX : FreeOf2 b X)
    (k : Fin 2) (z : Ix S) : ((Rht0 b d * X : M2 (SlopeTestRemainingChoices S A)) 0 k) z e1 = (X 0 k) z e1 := by
  have h : (Rht0 b d * X : M2 (SlopeTestRemainingChoices S A)) 0 k =
      (d - 1)⁻¹ • (d • X 0 k - (eU b 0 0 * X 0 k + eU b 0 1 * X 1 k)) := by
    unfold Rht0
    rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Q0,
      Matrix.of_apply]
  rw [h]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, eU_mul_apply]
  have h1 : (X 1 k) (Function.update z b 1) e1 = 0 := by
    apply free_apply_zero (hX 1 k)
    simp [e1]
  by_cases hz : z b = 0
  · have hu : Function.update z b 0 = z := by rw [← hz]; exact Function.update_eq_self b z
    simp only [hz, if_true, h1, add_zero, hu]
    exact smul_cancel d hd _
  · have h0 : (X 0 k) z e1 = 0 := free_apply_zero (hX 0 k) hz
    simp [hz, h0]
end Formalism.FourierDecayAlt.P.Wd7
