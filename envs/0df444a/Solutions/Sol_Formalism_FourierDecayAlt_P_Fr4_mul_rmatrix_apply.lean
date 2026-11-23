-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.mul_rmatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:05.598882+00:00
-- url     : https://prove2.me/submissions/ef398e0e-2918-4ab4-8dbb-6d9d51f484e0

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr4
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr4
theorem _root_.solution (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) (i j : Fin 2) :
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • M i j - (M i 0 * eU a j 0 + M i 1 * eU a j 1)) := by
  unfold Rh0 P0
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_sub, Matrix.sub_apply, Matrix.mul_smul, Matrix.smul_apply,
    Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_two]
  rfl
end Formalism.FourierDecayAlt.P.Fr4
