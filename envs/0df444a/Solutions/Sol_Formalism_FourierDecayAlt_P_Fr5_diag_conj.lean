-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.diag_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:24.456304+00:00
-- url     : https://prove2.me/submissions/4cccc704-937d-4a26-97fd-2cc1dba3c966

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
theorem _root_.solution (x y : SlopeTestRemainingChoices S A) : (!![x, 0; 0, y] : M2 (SlopeTestRemainingChoices S A))ᴴ = !![star x, 0; 0, star y] := by
  first
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> simp)
  | (ext i j; fin_cases i <;> fin_cases j <;> simp)
end Formalism.FourierDecayAlt.P.Fr5
