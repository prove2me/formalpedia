-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.Rht0_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:43.595386+00:00
-- url     : https://prove2.me/submissions/4d40cd24-ab28-45c7-abbc-ea8d5c3f44ba

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
theorem _root_.solution (b : S) (M : M2 (SlopeTestRemainingChoices S A)) (d : ℂ) (i j : Fin 2) :
    (Rht0 b d * M : M2 (SlopeTestRemainingChoices S A)) i j =
      (d - 1)⁻¹ • (d • M i j - (eU b i 0 * M 0 j + eU b i 1 * M 1 j)) := by
  unfold Rht0 Q0
  rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.smul_apply,
    Matrix.one_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rfl
end Formalism.FourierDecayAlt.P.Fr4
