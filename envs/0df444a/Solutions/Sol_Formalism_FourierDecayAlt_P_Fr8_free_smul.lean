-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.free_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:53.109649+00:00
-- url     : https://prove2.me/submissions/7a436961-354b-48e8-a807-cc7e7a5c161e

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
theorem _root_.solution [Algebra ℂ A] {c : S} {b : SlopeTestRemainingChoices S A} (k : ℂ) (h : FreeOf c b) : FreeOf c (k • b) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at h ⊢
  intro i j
  exact (h i j).smul_right k
end Formalism.FourierDecayAlt.P.Fr8
