-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.star_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:38.290608+00:00
-- url     : https://prove2.me/submissions/7c6818c3-bc47-4068-82c3-df19c4bbf74f

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m__99f5b295c9de
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mGi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_star__b_4314c298a3a0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_star_GGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_star


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
variable (L : LevelData A r)
variable {L}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (hS : IsStarLevel L) : star (wt L : SlopeTestRemainingChoices S A) = wt L := by
  unfold wt
  rw [Wd11.io_star, star_mul, star_mul, star_GGi hS, star_ζb hS, hS.1]
  congr 1
  rw [← mul_assoc, zc L (mGi L) (mζ L), mul_assoc, zc L (mGi L) (mζb L), ← mul_assoc]
end Formalism.FourierDecayAlt.P.Fr9
