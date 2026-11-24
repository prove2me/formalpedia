-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.zetaBarInv_commute_l0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:25.150264+00:00
-- url     : https://prove2.me/submissions/646119a2-e20d-4ce5-bb64-69b2388cbfe5

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_l0_eq_neg_nabla_sub

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
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (Y : ℂ) : L.ζbi * L.l0 Y = L.l0 Y * L.ζbi := by
  rw [l0_eq_neg_nabla_sub]
  have e : L.ζbi * (L.ζb * L.GGi) = L.ζb * L.GGi * L.ζbi := by
    rw [← mul_assoc, zc L (mζbi L) (mζb L), mul_assoc, zc L (mζbi L) (mGi L), mul_assoc]
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, e, mul_neg, neg_mul, L.nab_ζbi]
end Formalism.FourierDecayAlt.P.Fr9
