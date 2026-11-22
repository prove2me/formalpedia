-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.mul_io_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:06.339796+00:00
-- url     : https://prove2.me/submissions/9f6be2c2-f18e-4dae-b81f-3c30487586f0

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
theorem _root_.solution (x : A) (M : SlopeTestRemainingChoices S A) (z y : Ix S) : (M * (io x : SlopeTestRemainingChoices S A)) z y = M z y * x := by
  simp [io, Matrix.scalar_apply, Matrix.mul_diagonal]
end Formalism.FourierDecayAlt.P.Wd7
