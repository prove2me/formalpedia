-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.free_io
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:06:51.134534+00:00
-- url     : https://prove2.me/submissions/5b2125d1-a42b-454e-ae6a-c3d58c2f3c7a

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf
  intro i j
  show Formalism.FourierDecayAlt.Wd.eU c i j * Formalism.FourierDecayAlt.Wd.io x = Formalism.FourierDecayAlt.Wd.io x * Formalism.FourierDecayAlt.Wd.eU c i j
  simp only [Formalism.FourierDecayAlt.Wd.io, Matrix.scalar_apply]
  refine Matrix.ext fun u v => ?_
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Formalism.FourierDecayAlt.Wd.eU, Matrix.of_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Fr8
