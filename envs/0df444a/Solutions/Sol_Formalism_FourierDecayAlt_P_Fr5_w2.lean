-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.w2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:02:58.911678+00:00
-- url     : https://prove2.me/submissions/0caa8d21-5082-4cbf-8f3e-c919e1da9fe5

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_fn_comm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__b_4a242cf5d7ab
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
theorem _root_.solution (L : LevelData A r) : L.GG * L.ζi * (L.ζ * L.ζb * L.GGi) * (L.ζbi * L.GG) = L.GG := by
  have c3 : L.ζb * L.GGi = L.GGi * L.ζb := fn_comm L (mem_ζb L) (mem_GGi L)
  calc L.GG * L.ζi * (L.ζ * L.ζb * L.GGi) * (L.ζbi * L.GG)
        = L.GG * (L.ζi * L.ζ) * (L.ζb * L.GGi) * (L.ζbi * L.GG) := by simp only [mul_assoc]
    _ = L.GG * L.GGi * (L.ζb * L.ζbi) * L.GG := by rw [L.ζi_ζ, mul_one, c3]; simp only [mul_assoc]
    _ = L.GG := by rw [L.GG_GGi, L.ζb_ζbi, one_mul, one_mul]
end Formalism.FourierDecayAlt.P.Fr5
