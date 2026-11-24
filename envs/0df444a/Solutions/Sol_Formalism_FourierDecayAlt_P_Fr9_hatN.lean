-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.hatN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:19.114786+00:00
-- url     : https://prove2.me/submissions/51347897-4be7-4667-a46c-5b0b1694a680

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_hat_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_d0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mk2

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
theorem _root_.solution (h : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) (c d : ℂ) (j : Fin 2) :
    d0 f.F * (c • !![d • f.TT Y 1 j, 0; -f.TT Y 0 j, (d - 1) • f.TT Y 1 j]) =
      (c • !![d • f.hatT Y 1 j, 0; -f.hatT Y 0 j, (d - 1) • f.hatT Y 1 j]) * d0 f.F := by
  rw [d0_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  refine mk2 ?_ ?_ ?_ ?_
  · rw [zero_mul, zero_mul, add_zero, add_zero, mul_smul_comm, smul_mul_assoc, hat_F h hY]
  · simp
  · rw [zero_mul, mul_zero, zero_add, add_zero, mul_neg, neg_mul, hat_F h hY]
  · rw [zero_mul, mul_zero, zero_add, zero_add, mul_smul_comm, smul_mul_assoc, hat_F h hY]
end Formalism.FourierDecayAlt.P.Fr9
