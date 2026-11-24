-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.free_Vw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:28:53.691809+00:00
-- url     : https://prove2.me/submissions/317736dd-e2bc-4ed4-a60f-9a2c9b15c0fd

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_UUiw

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
theorem _root_.solution (f : A) (s : K) (w : List (Letter K S)) (c : S) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (Vw f s w) := free_mul (free_io c f) (free_UUiw s w c hc)
end Formalism.FourierDecayAlt.P.Wd11
