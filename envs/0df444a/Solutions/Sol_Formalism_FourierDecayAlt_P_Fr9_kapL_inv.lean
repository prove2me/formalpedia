-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.kapL_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:33.737125+00:00
-- url     : https://prove2.me/submissions/21783f1b-d2ef-4803-abb7-7420e285b6bf

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
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
theorem _root_.solution : (io (L.GG * L.ζ * L.ζbi) : SlopeTestRemainingChoices S A) * kapL L = 1 := by
  unfold kapL
  rw [← Wd11.io_mul, ← Wd11.io_one]
  congr 1
  calc L.GG * L.ζ * L.ζbi * (L.ζb * L.ζi * L.GGi) = L.GG * (L.ζ * (L.ζbi * L.ζb) * L.ζi) * L.GGi := by
        simp only [mul_assoc]
    _ = 1 := by rw [L.ζbi_ζb, mul_one, L.ζ_ζi, mul_one, L.GG_GGi]
end Formalism.FourierDecayAlt.P.Fr9
