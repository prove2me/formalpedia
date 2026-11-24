-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.comm_io_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:29.443802+00:00
-- url     : https://prove2.me/submissions/71ca30a5-9823-448c-bd20-7bb8c99cfec2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution (C : SlopeTestRemainingChoices S A) (c : ℂ) : Commute C (io (algebraMap ℂ A c)) := by
  refine Matrix.ext fun z z' => ?_
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (Algebra.commutes c (C z z')).symm
end Formalism.FourierDecayAlt.P.FreeActionExpansion
