-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.star_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:27.938575+00:00
-- url     : https://prove2.me/submissions/6677c82c-146d-4c9c-bfa0-9d338893b15c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_fcomm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m__071036119794
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_b_8bb7912692ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mGGi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_star__b_8b8b591566b9
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_star_GGi

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
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star (wt L : SlopeTestRemainingChoices S A) = wt L := by
  obtain ⟨h1, -, -⟩ := id h
  rw [Formalism.FourierDecayAlt.Fr.wt, io_star]
  congr 1
  rw [star_mul, star_mul, star_GGi h, star_ζb h, h1]
  exact ((fcomm L (mGGi L) (mζ L)).mul_right (fcomm L (mGGi L) (mζb L))).eq
end Formalism.FourierDecayAlt.P.Fr8
