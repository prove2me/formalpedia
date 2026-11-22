-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.io_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:29.426531+00:00
-- url     : https://prove2.me/submissions/0cb34195-f47d-4a7e-89a9-2b79a29bf5c3

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry

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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (x : A) (M : SlopeTestRemainingChoices S A) (z y : Ix S) : ((io x : SlopeTestRemainingChoices S A) * M) z y = x * M z y := by
  simp [io, Matrix.scalar_apply, Matrix.diagonal_mul]
end Formalism.FourierDecayAlt.P.Wd7
