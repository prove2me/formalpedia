-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.zeta_conj_nabla
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:22.835933+00:00
-- url     : https://prove2.me/submissions/3c46b15e-9bb9-4689-9b70-93c8cb4b7e99

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m__58fce9a2b273
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_i_b8c0bb40777f
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_b_af699ddbdd9f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zetaInv_mul_l0_mul_zeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zetaConj2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Fr3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.ZetaConj := by
  intro A S _ _ _ _ _ _ r L f Y hee
  refine ⟨?_, zetaConj2 L⟩
  have c : Commute (kapL L * f.ee Y : SlopeTestRemainingChoices S A) (io L.ζ) := by
    refine Commute.mul_left ?_ (hee _ (mζ L))
    exact io_comm (((zc L (mζb L) (mζ L)).mul_left (zc L (mζi L) (mζ L))).mul_left (zc L (mGGi L) (mζ L)))
  have i1 : (io L.ζi : SlopeTestRemainingChoices S A) * io L.ζ = 1 := by rw [← io_mul, L.ζi_ζ, io_one]
  have h1 : (io L.ζi : SlopeTestRemainingChoices S A) * io (L.l0 Y) * io L.ζ = io (L.l0 Y) - io L.ζi := by
    rw [← io_mul, ← io_mul, zetaInv_mul_l0_mul_zeta]; simp only [io, map_sub]
  have h2 : (io L.ζi : SlopeTestRemainingChoices S A) * (kapL L * f.ee Y) * io L.ζ = kapL L * f.ee Y := by
    rw [mul_assoc, c.eq, ← mul_assoc, i1, one_mul]
  unfold FrameData.l
  rw [mul_add, add_mul, h1, h2]; abel
end Formalism.FourierDecayAlt.P
