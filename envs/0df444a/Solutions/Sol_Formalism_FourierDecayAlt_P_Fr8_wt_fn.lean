-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.wt_fn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:19.869478+00:00
-- url     : https://prove2.me/submissions/d016e135-cce1-4b04-8230-533a2e312faa

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_comm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m__071036119794
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_b_8bb7912692ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mGGi

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
theorem _root_.solution (L : LevelData A r) {g : A} (hg : g ∈ zfns L) : Commute (wt L : SlopeTestRemainingChoices S A) (io g) := by
  unfold Formalism.FourierDecayAlt.Fr.wt
  exact io_comm (((fcomm L (mζ L) hg).mul_left (fcomm L (mζb L) hg)).mul_left (fcomm L (mGGi L) hg))
end Formalism.FourierDecayAlt.P.Fr8
