-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.comm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:31:33.856641+00:00
-- url     : https://prove2.me/submissions/343c1837-7677-49c7-9d91-231eca12af40

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_GlobalTheory_CommuteInvLeft_commute_inv_left


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
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Fr10
theorem _root_.solution {x xi y : B} (h1 : x * xi = 1) (h2 : xi * x = 1) (h : Commute x y) : Commute xi y := by
  first | exact GlobalTheory.CommuteInvLeft.commute_inv_left .. | (apply GlobalTheory.CommuteInvLeft.commute_inv_left <;> assumption) | (intros; apply GlobalTheory.CommuteInvLeft.commute_inv_left <;> assumption) | (apply @GlobalTheory.CommuteInvLeft.commute_inv_left <;> assumption) | (intros; apply @GlobalTheory.CommuteInvLeft.commute_inv_left <;> assumption) | (apply @GlobalTheory.CommuteInvLeft.commute_inv_left <;> first | assumption | infer_instance) | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi y h1 h2 h | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi y h1 h2 | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi y h1 | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi y | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B
end Formalism.FourierDecayAlt.P.Fr10
