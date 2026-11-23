-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.freeOf2_of_four_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:37:06.185601+00:00
-- url     : https://prove2.me/submissions/98c2d51b-a9a4-4502-a77e-5d05371cd487

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
theorem _root_.solution {a : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) (hz : FreeOf a z)
    (hw : FreeOf a w) : FreeOf2 a !![x, y; z, w] := by
  intro i j
  fin_cases i <;> fin_cases j <;> first | exact hx | exact hy | exact hz | exact hw | simp [hx, hy, hz, hw]
end Formalism.FourierDecayAlt.P.Fr5
