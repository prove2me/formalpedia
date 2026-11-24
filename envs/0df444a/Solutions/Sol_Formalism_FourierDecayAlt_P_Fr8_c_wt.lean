-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.c_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:49.21386+00:00
-- url     : https://prove2.me/submissions/36fe6c91-f502-47bc-a0a8-ce6e50d8cc09

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m__071036119794
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_b_8bb7912692ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mGGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_wt_eq

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
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution (h : IsFrame L f) : Commute f.c (wt L) := by
  rw [wt_eq]
  exact ((h.c_fn _ (mζ L)).mul_right (h.c_fn _ (mζb L))).mul_right (h.c_fn _ (mGGi L))
end Formalism.FourierDecayAlt.P.Fr8
