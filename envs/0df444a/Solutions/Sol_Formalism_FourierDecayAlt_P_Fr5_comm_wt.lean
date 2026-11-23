-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.comm_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:40.713789+00:00
-- url     : https://prove2.me/submissions/dfbde625-2f8d-4c17-aea2-3c271ebf3756

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem___d82dc59c5260
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__b_4a242cf5d7ab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_mem_GGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_wt_eq

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
theorem _root_.solution (L : LevelData A r) {b : SlopeTestRemainingChoices S A} (h : ∀ g ∈ zfns L, Commute b (io g)) : Commute b (wt L) := by
  rw [wt_eq]
  exact ((h _ (mem_ζ L)).mul_right (h _ (mem_ζb L))).mul_right (h _ (mem_GGi L))
end Formalism.FourierDecayAlt.P.Fr5
