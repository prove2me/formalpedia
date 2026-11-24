-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.io_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:51:07.063146+00:00
-- url     : https://prove2.me/submissions/28f84514-0d00-4a17-892e-7e6a04d7a707

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution [StarRing A] (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  unfold io
  rw [Matrix.star_eq_conjTranspose, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_conjTranspose]
  rfl
end Formalism.FourierDecayAlt.P.Wd11
