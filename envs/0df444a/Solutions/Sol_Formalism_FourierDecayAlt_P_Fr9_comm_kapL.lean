-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.comm_kapL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:17.493674+00:00
-- url     : https://prove2.me/submissions/554fe17a-afd8-48c4-8770-8b3c0e853c2c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
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
theorem _root_.solution {y : SlopeTestRemainingChoices S A} (hy : ∀ g ∈ zfns L, Commute y (io g)) : Commute y (kapL L) := by
  unfold kapL
  rw [Wd11.io_mul, Wd11.io_mul]
  exact ((hy _ (mζb L)).mul_right (hy _ (mζi L))).mul_right (hy _ (mGi L))
end Formalism.FourierDecayAlt.P.Fr9
