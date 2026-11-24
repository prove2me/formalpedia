-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.rhs_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:03.679547+00:00
-- url     : https://prove2.me/submissions/234e1802-c9c7-4492-929a-3934bcbe4c6b

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_ins_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul


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
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution {F : SlopeTestRemainingChoices S A} {P W : M2 (SlopeTestRemainingChoices S A)} (hW : FreeOf2 b W) :
    ins b W * (ins b P * F) = ins b (W * P * d0 F) := by
  rw [← mul_assoc, ← Wd1.ins_mul _ _ _ hW, ins_right]
end Formalism.FourierDecayAlt.P.Fr9
