-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:33.543923+00:00
-- url     : https://prove2.me/submissions/ce7242fa-c787-4a61-9aa1-ea05b1b61994

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_mul

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
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution (L : LevelData A r) : (wt L : SlopeTestRemainingChoices S A) = io L.ζ * io L.ζb * io L.GGi := by
  simp only [Formalism.FourierDecayAlt.Fr.wt, io_mul]
end Formalism.FourierDecayAlt.P.Fr8
