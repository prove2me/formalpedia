-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.inv_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:11.776268+00:00
-- url     : https://prove2.me/submissions/0f0d099f-5fa5-49f5-9c54-de9d97f720ac

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_one


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
theorem _root_.solution {a : S} {u ui : SlopeTestRemainingChoices S A} {M Mi : M2 (SlopeTestRemainingChoices S A)} (fui : FreeOf a ui) (fM : FreeOf2 a M)
    (h : u * ui = 1) (hc : ∀ i j, Commute ui (M i j)) (hM : M * Mi = 1) :
    u * ins a M * (ui * ins a Mi) = 1 := by
  calc u * ins a M * (ui * ins a Mi) = u * (ins a M * ui) * ins a Mi := by simp only [mul_assoc]
    _ = u * (ui * ins a M) * ins a Mi := by rw [(ins_comm a M ui fui hc).eq]
    _ = (u * ui) * (ins a M * ins a Mi) := by simp only [mul_assoc]
    _ = 1 := by rw [h, one_mul, ← ins_mul a M Mi fM, hM, ins_one]
end Formalism.FourierDecayAlt.P.Fr10
