-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.zetaInv_GG_conj_l0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:26.127253+00:00
-- url     : https://prove2.me/submissions/2207fe00-8cdb-465e-a2d0-09717310cf37

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mG
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
theorem _root_.solution (Y : ℂ) :
    L.ζi * L.GG * L.l0 Y = (L.l0 Y + L.TT • (L.ζi * L.GGi)) * (L.ζi * L.GG) := by
  rw [l0_eq_neg_nabla_sub]
  have e : L.ζi * L.GG * (L.ζb * L.GGi) = L.ζb * L.GGi * (L.ζi * L.GG) := by
    rw [zc L (mζi L) (mG L), zc L (mζb L) (mGi L)]
    calc L.GG * L.ζi * (L.GGi * L.ζb) = L.GG * (L.ζi * L.GGi) * L.ζb := by simp only [mul_assoc]
      _ = (L.GG * L.GGi) * (L.ζi * L.ζb) := by rw [zc L (mζi L) (mGi L)]; simp only [mul_assoc]
      _ = (L.GGi * L.GG) * (L.ζb * L.ζi) := by rw [L.GG_GGi, L.GGi_GG, zc L (mζi L) (mζb L)]
      _ = L.GGi * (L.GG * L.ζb) * L.ζi := by simp only [mul_assoc]
      _ = L.GGi * L.ζb * (L.GG * L.ζi) := by rw [zc L (mG L) (mζb L)]; simp only [mul_assoc]
  have e2 : L.nab * (L.ζi * L.GG) = L.ζi * L.GG * L.nab + L.ζi * L.ζb - L.ζi * L.ζi * L.GG := by
    rw [← mul_assoc, L.nab_ζi, sub_mul, mul_assoc, L.nab_GG, mul_add, ← mul_assoc]
  have e3 : L.ζi * L.GGi * (L.ζi * L.GG) = L.ζi * L.ζi := by
    rw [mul_assoc, ← mul_assoc L.GGi, zc L (mGi L) (mζi L), mul_assoc, L.GGi_GG, mul_one]
  have e4 : L.ζi * L.ζi * L.GG = L.ζi * L.ζb - L.TT • (L.ζi * L.ζi) := by
    rw [L.GG_def, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, mul_assoc, ← mul_assoc L.ζi L.ζ, L.ζi_ζ,
      one_mul]
  rw [mul_sub, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, e, mul_neg, neg_mul, e2, e3, e4]
  abel
end Formalism.FourierDecayAlt.P.Fr9
