-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.freeOf_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:45.343257+00:00
-- url     : https://prove2.me/submissions/42733882-5736-4b43-a93a-c0de744924bd

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {a : S}
namespace Formalism.FourierDecayAlt.P.Fr7
theorem _root_.solution (φ : ℂ) : FreeOf a (φ • (1 : SlopeTestRemainingChoices S A)) :=
  free_smul φ free_one
end Formalism.FourierDecayAlt.P.Fr7
