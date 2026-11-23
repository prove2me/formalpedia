-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.comm_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:59.307992+00:00
-- url     : https://prove2.me/submissions/e0c30886-636a-452f-a134-84c747aad85c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_comm_wt

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
theorem _root_.solution (L : LevelData A r) (f : FrameData S A) {b : SlopeTestRemainingChoices S A} (h1 : ∀ g ∈ zfns L, Commute b (io g))
    (h2 : Commute b f.c) : Commute b (f.d L) := by
  have e : f.d L = wt L ^ f.N * f.c := rfl
  rw [e]
  exact ((comm_wt L h1).pow_right f.N).mul_right h2
end Formalism.FourierDecayAlt.P.Fr5
