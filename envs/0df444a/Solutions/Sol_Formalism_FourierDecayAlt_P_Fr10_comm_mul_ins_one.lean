-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.comm_mul_ins_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:06.694875+00:00
-- url     : https://prove2.me/submissions/bd318aec-c5c2-4c5c-8783-268ed7cc6268

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr10
theorem _root_.solution {a : S} {u w : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (fw : FreeOf a w) (huw : Commute u w)
    (hwM : ∀ i j, Commute w (M i j)) : Commute (u * ins a M) w :=
  Commute.mul_left huw (ins_comm a M w fw hwM).symm
end Formalism.FourierDecayAlt.P.Fr10
