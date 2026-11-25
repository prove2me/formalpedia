-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.h_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:55.469512+00:00
-- url     : https://prove2.me/submissions/4fc771d0-e62a-416f-a437-cfb049ae039c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mGi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_kapL__bi_88427ab3dc72
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_one


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
theorem _root_.solution {X1 X2 : SlopeTestRemainingChoices S A} (h1 : ∀ g ∈ zfns L, Commute X1 (io g)) (h2 : ∀ g ∈ zfns L, Commute X2 (io g))
    (h12 : Commute X1 X2) (c q : ℂ) :
    io L.ζi * io L.GG * -(c⁻¹ • q • (io L.GGi * X1 * (io L.GGi * X2))) =
      -(kapL L * ((q / c) • (X2 * X1))) * io L.ζbi := by
  have gg1 : (io L.GG : SlopeTestRemainingChoices S A) * io L.GGi = 1 := by rw [← Wd11.io_mul, L.GG_GGi, Wd11.io_one]
  have a : io L.ζi * io L.GG * (io L.GGi * X1 * (io L.GGi * X2)) = io L.ζi * io L.GGi * (X2 * X1) := by
    calc io L.ζi * io L.GG * (io L.GGi * X1 * (io L.GGi * X2))
        = io L.ζi * (io L.GG * io L.GGi) * (X1 * io L.GGi) * X2 := by simp only [mul_assoc]
      _ = io L.ζi * io L.GGi * (X1 * X2) := by rw [gg1, mul_one, (h1 _ (mGi L)).eq]; simp only [mul_assoc]
      _ = _ := by rw [h12.eq]
  have b : kapL L * (X2 * X1) * io L.ζbi = io L.ζi * io L.GGi * (X2 * X1) := by
    rw [mul_assoc, ((h2 _ (mζbi L)).mul_left (h1 _ (mζbi L))).eq, ← mul_assoc, kapL_ζbi]
  rw [mul_neg, neg_mul, mul_smul_comm, mul_smul_comm, a, mul_smul_comm, smul_mul_assoc, b, smul_smul,
    div_eq_inv_mul]
end Formalism.FourierDecayAlt.P.Fr9
