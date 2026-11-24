-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.ins_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:32:18.173999+00:00
-- url     : https://prove2.me/submissions/12d0fde7-7bcb-454f-ac33-fff72bb5ac3f

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_d0_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_ins_sandwich


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
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (b : S) (M : M2 (SlopeTestRemainingChoices S A)) (y : SlopeTestRemainingChoices S A) :
    ins b M * y = ins b (M * d0 y) := by
  have h := Wd11.ins_sandwich (Wd11.free_one b) M y
  rw [Wd11.d0_one, one_mul, one_mul] at h
  exact h.symm
end Formalism.FourierDecayAlt.P.Fr9
