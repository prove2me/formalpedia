-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.comm_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:50:38.576116+00:00
-- url     : https://prove2.me/submissions/f0e2773a-5371-4340-a7ad-2af7a67094bb

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
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution {f fi x : A} (h1 : f * fi = 1) (h2 : fi * f = 1) (h : x * fi = fi * x) :
    f * x = x * f := by
  calc f * x = f * (x * fi) * f := by rw [mul_assoc, mul_assoc, h2, mul_one]
    _ = f * fi * x * f := by rw [h]; simp only [mul_assoc]
    _ = x * f := by rw [h1, one_mul]
end Formalism.FourierDecayAlt.P.Wd11
