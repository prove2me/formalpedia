-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.freeOf_diagScalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:58.239992+00:00
-- url     : https://prove2.me/submissions/33180cf2-94ba-4cc8-ad08-50b542a9364e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) : FreeOf2 a (d0 b) := by
  intro i j
  unfold d0
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hb
  · exact fun _ _ => Commute.zero_right _
end Formalism.FourierDecayAlt.P.Wd4
