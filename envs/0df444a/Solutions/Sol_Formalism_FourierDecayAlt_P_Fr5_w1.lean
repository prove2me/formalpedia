-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.w1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:52.548675+00:00
-- url     : https://prove2.me/submissions/8658b2eb-e761-4588-8a33-248450758e11

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_fn_comm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem___d82dc59c5260
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__i_7172e6a0b2cd
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__bi_956546b22979
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_mem_GGi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution (L : LevelData A r) : L.ζbi * (L.ζ * L.ζb * L.GGi) * L.ζi = L.GGi := by
  have c1 : L.ζbi * L.ζ = L.ζ * L.ζbi := fn_comm L (mem_ζbi L) (mem_ζ L)
  have c2 : L.GGi * L.ζi = L.ζi * L.GGi := fn_comm L (mem_GGi L) (mem_ζi L)
  calc L.ζbi * (L.ζ * L.ζb * L.GGi) * L.ζi = L.ζ * (L.ζbi * L.ζb) * (L.GGi * L.ζi) := by
        rw [← mul_assoc L.ζbi, ← mul_assoc L.ζbi, c1]; simp only [mul_assoc]
    _ = L.GGi := by rw [L.ζbi_ζb, mul_one, c2, ← mul_assoc, L.ζ_ζi, one_mul]
end Formalism.FourierDecayAlt.P.Fr5
