-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.commute_level_zero_element
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:18.322435+00:00
-- url     : https://prove2.me/submissions/d570154e-558f-41c2-bfb9-850fde814906

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_l0_eq_neg_nabla_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_neg


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
theorem _root_.solution {y : SlopeTestRemainingChoices S A} (hy : ∀ g ∈ zfns L, Commute y (io g)) (hn : Commute y (io L.nab)) (Y : ℂ) :
    Commute y (io (L.l0 Y)) := by
  rw [l0_eq_neg_nabla_sub, io_sub, Wd11.io_neg, io_smul, Wd11.io_mul]
  exact hn.neg_right.sub_right (((hy _ (mζb L)).mul_right (hy _ (mGi L))).smul_right _)
end Formalism.FourierDecayAlt.P.Fr9
