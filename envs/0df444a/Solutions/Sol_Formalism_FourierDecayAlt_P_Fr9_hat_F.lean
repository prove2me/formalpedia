-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.hat_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:08.435599+00:00
-- url     : https://prove2.me/submissions/d4c13ba0-900b-46ca-869a-a8c1108016c3

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_hat_reg

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
theorem _root_.solution (h : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) (i j : Fin 2) :
    f.hatT Y i j * f.F = f.F * f.TT Y i j := by
  rw [hat_reg hY, mul_assoc, h.Fi_F, mul_one]
end Formalism.FourierDecayAlt.P.Fr9
