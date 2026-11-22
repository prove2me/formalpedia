-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.io_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:55.765319+00:00
-- url     : https://prove2.me/submissions/f4a1dad3-8da5-4587-957d-0d3c4cb8b7ca

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  first
  | exact Matrix.diagonal_conjTranspose (fun _ : Ix S => x)
  | (show star (Matrix.scalar (Ix S) x) = Matrix.scalar (Ix S) (star x)
     simp [Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]; rfl)
end Formalism.FourierDecayAlt.P.Fr5
