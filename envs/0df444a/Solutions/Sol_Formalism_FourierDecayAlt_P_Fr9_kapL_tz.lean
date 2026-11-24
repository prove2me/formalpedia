-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.kapL_tz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:24.216669+00:00
-- url     : https://prove2.me/submissions/e6b9ce30-b2d9-4896-9bb8-fe98cc64e2fc

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution : (kapL L : SlopeTestRemainingChoices S A) * tz L = io (L.TT • (L.ζi * L.GGi)) := by
  unfold kapL tz
  rw [← Wd11.io_mul, mul_smul_comm]
  congr 2
  rw [mul_assoc, mul_assoc, zc L (mGi L) (mζbi L), ← mul_assoc L.ζi, zc L (mζi L) (mζbi L), mul_assoc,
    ← mul_assoc, L.ζb_ζbi, one_mul]
end Formalism.FourierDecayAlt.P.Fr9
