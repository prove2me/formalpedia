-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.comm_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:58.288012+00:00
-- url     : https://prove2.me/submissions/eb827f4b-86b1-4ea2-89d2-f78324620fbe

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_ins_comm_ins
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
theorem _root_.solution {a : S} {u v : SlopeTestRemainingChoices S A} {M N : M2 (SlopeTestRemainingChoices S A)} (fu : FreeOf a u) (fv : FreeOf a v)
    (fM : FreeOf2 a M) (fN : FreeOf2 a N) (huv : Commute u v) (huN : ∀ i j, Commute u (N i j))
    (hvM : ∀ i j, Commute v (M i j)) (hMN : M * N = N * M) : Commute (u * ins a M) (v * ins a N) :=
  Commute.mul_left (huv.mul_right (ins_comm a N u fu huN))
    ((ins_comm a M v fv hvM).symm.mul_right (ins_comm_ins fM fN hMN))
end Formalism.FourierDecayAlt.P.Fr10
