-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.free_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:55.826614+00:00
-- url     : https://prove2.me/submissions/3a6c5288-b3b5-4bd5-8c82-be4d46931217

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
theorem _root_.solution (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _
end Formalism.FourierDecayAlt.P.Fr4
