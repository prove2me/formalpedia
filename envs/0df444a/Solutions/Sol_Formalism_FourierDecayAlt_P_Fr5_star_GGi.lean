-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.star_GGi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:06.978413+00:00
-- url     : https://prove2.me/submissions/b790c1cc-cbf0-47d2-8985-84a74eea66d3

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_star_GG

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
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star L.GGi = L.GGi := by
  calc star L.GGi = star L.GGi * (L.GG * L.GGi) := by rw [L.GG_GGi, mul_one]
    _ = star (L.GG * L.GGi) * L.GGi := by rw [star_mul, star_GG h, mul_assoc]
    _ = L.GGi := by rw [L.GG_GGi, star_one, one_mul]
end Formalism.FourierDecayAlt.P.Fr5
