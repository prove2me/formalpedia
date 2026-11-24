-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.wt_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:46.410819+00:00
-- url     : https://prove2.me/submissions/fbd72f89-4d83-4c22-8e0e-a1c58f1847f7

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m__58fce9a2b273
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_b_af699ddbdd9f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGGi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_star__b_1c4832101cb0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_star_GGi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution (hL : IsStarLevel L) : star (wt L : SlopeTestRemainingChoices S A) = wt L := by
  unfold wt
  rw [io_star, star_mul, star_mul, hL.1, star_ζb hL, star_GGi hL,
    ((zc L (mGGi L) (mζ L)).mul_right (zc L (mGGi L) (mζb L))).eq]
end Formalism.FourierDecayAlt.P.Fr3
