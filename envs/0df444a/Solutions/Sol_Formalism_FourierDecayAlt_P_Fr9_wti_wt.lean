-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.wti_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:26:33.775809+00:00
-- url     : https://prove2.me/submissions/db15d102-a012-4982-bfe2-c0b43d5f67a7

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m__99f5b295c9de
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
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
theorem _root_.solution : (wti L : SlopeTestRemainingChoices S A) * wt L = 1 := by
  unfold wti wt
  rw [← Wd11.io_mul, ← Wd11.io_one]
  congr 1
  calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = L.GG * (L.ζi * (L.ζbi * L.ζ) * L.ζb) * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * ((L.ζi * L.ζ) * (L.ζbi * L.ζb)) * L.GGi := by
        rw [zc L (mζbi L) (mζ L)]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]
end Formalism.FourierDecayAlt.P.Fr9
