-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.star_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:07.416569+00:00
-- url     : https://prove2.me/submissions/e497d0b8-fb00-44c0-be8d-d0a7283cc1e8

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star


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
theorem _root_.solution {a : S} {u : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (fu : FreeOf a u) (fM : FreeOf2 a M)
    (hu : star u = u) (hc : ∀ i j, Commute u (M i j)) (hM : Mᴴ = M) : star (u * ins a M) = u * ins a M := by
  rw [star_mul, ins_star a M fM, hM, hu, (ins_comm a M u fu hc).eq]
end Formalism.FourierDecayAlt.P.Fr10
