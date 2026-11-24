-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.diag_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:24.522069+00:00
-- url     : https://prove2.me/submissions/08d7e753-e37a-44dc-96f2-43336c9f0ccf

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_d0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mk2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_smul_matrix2_of

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
variable {b : S}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (τ : SlopeTestRemainingChoices S A) {d : ℂ} (hd : d - 1 ≠ 0) :
    d0 τ * !![(d / (d - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] = (d - 1)⁻¹ • !![d • τ, 0; 0, (d - 1) • τ] := by
  rw [d0_eq, Matrix.mul_fin_two, smul_matrix2_of]
  refine mk2 ?_ ?_ ?_ ?_
  · rw [zero_mul, add_zero, mul_smul_comm, mul_one, smul_smul, div_eq_inv_mul]
  · simp
  · simp
  · rw [zero_mul, zero_add, mul_one, smul_smul, inv_mul_cancel₀ hd, one_smul]
end Formalism.FourierDecayAlt.P.Fr9
