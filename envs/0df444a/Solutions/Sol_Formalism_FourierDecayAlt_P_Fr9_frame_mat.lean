-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.frame_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:07.61831+00:00
-- url     : https://prove2.me/submissions/003275e4-d490-4580-b824-ce343de2b64d

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mk2

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
variable {b : S}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (L : LevelData A r) (m : SlopeTestRemainingChoices S A) :
    (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζbi, 0; io L.ζi * io L.GG * m, io L.ζi * io L.GG] := by
  rw [Matrix.mul_fin_two]
  refine mk2 ?_ ?_ ?_ ?_ <;> simp [mul_assoc]
end Formalism.FourierDecayAlt.P.Fr9
