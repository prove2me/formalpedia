-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.wti_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:25:23.239805+00:00
-- url     : https://prove2.me/submissions/1cf53f85-0541-466a-9e26-d5dfc06075f5

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mon3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_fcomm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m__071036119794
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_bi_189708a67289

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
theorem _root_.solution (L : LevelData A r) : (wti L : SlopeTestRemainingChoices S A) * wt L = 1 := by
  rw [Formalism.FourierDecayAlt.Fr.wti, Formalism.FourierDecayAlt.Fr.wt, ← io_mul, ← io_one]
  congr 1
  exact mon3 L.ζi_ζ L.ζbi_ζb L.GG_GGi (fcomm L (mζbi L) (mζ L))
end Formalism.FourierDecayAlt.P.Fr8
