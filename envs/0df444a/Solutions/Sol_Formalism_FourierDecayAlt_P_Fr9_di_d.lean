-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.di_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:50.99571+00:00
-- url     : https://prove2.me/submissions/094b6e75-b4c2-41ba-a37d-6cb827232009

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_wti_wt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_wt_wti

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
theorem _root_.solution (h : IsFrame L f) : f.di L * f.d L = 1 := by
  unfold FrameData.di FrameData.d
  have c : Commute (wti L : SlopeTestRemainingChoices S A) (wt L) := by
    show _ = _
    rw [wti_wt, wt_wti]
  calc f.ci * wti L ^ f.N * (wt L ^ f.N * f.c) = f.ci * (wti L ^ f.N * wt L ^ f.N) * f.c := by
        simp only [mul_assoc]
    _ = 1 := by rw [← c.mul_pow, wti_wt, one_pow, mul_one, h.c_ci.2]
end Formalism.FourierDecayAlt.P.Fr9
