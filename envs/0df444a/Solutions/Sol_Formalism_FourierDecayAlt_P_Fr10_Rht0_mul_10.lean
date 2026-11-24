-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.Rht0_mul_10
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:09.732799+00:00
-- url     : https://prove2.me/submissions/654661f7-88f9-4b74-b0fc-b3a4e605a5ad

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr10
theorem _root_.solution (b : S) (d : ℂ) (M : M2 (SlopeTestRemainingChoices S A)) :
    (Rht0 b d * M : M2 (SlopeTestRemainingChoices S A)) 1 0 = (d - 1)⁻¹ • ins b !![d • M 1 0, 0; -M 0 0, (d - 1) • M 1 0] := by
  have h := sum_eU_diag (A := A) b
  rw [Fin.sum_univ_two] at h
  have h0 : (eU b 0 0 : SlopeTestRemainingChoices S A) = 1 - eU b 1 1 := eq_sub_of_add_eq h
  unfold Rht0 ins Q0
  rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply]
  congr 1
  simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply_eq]
  simp [h0, sub_mul, mul_sub, sub_smul]
  module
end Formalism.FourierDecayAlt.P.Fr10
