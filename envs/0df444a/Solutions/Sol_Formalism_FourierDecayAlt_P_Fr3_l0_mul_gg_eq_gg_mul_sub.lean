-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.l0_mul_gg_eq_gg_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:59.507311+00:00
-- url     : https://prove2.me/submissions/c673a006-8b75-47cb-b506-397ad9a13abc

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_b_af699ddbdd9f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_l0_constant_part_commute

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
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution (Y : ℂ) : L.l0 Y * L.GG = L.GG * (L.l0 Y - L.ζb * L.GGi) := by
  have c := l0_constant_part_commute L Y (mGG L)
  have h : L.GG * (L.ζb * L.GGi) = L.ζb := by
    rw [(zc L (mζb L) (mGGi L)).eq, ← mul_assoc, L.GG_GGi, one_mul]
  unfold LevelData.l0
  rw [sub_mul, c.eq, neg_mul, L.nab_GG, mul_sub, mul_sub, h, mul_neg]; abel
end Formalism.FourierDecayAlt.P.Fr3
