-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.comm_sc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:48.841521+00:00
-- url     : https://prove2.me/submissions/15efb097-02d6-4bf5-8853-f119f55ecd5b

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_comm_lit

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
theorem _root_.solution (w : SlopeTestRemainingChoices S A) (α : ℂ) : ∀ i j, Commute w ((!![α • 1, 0; 0, 1] : M2 (SlopeTestRemainingChoices S A)) i j) :=
  comm_lit ((Commute.one_right w).smul_right α) (Commute.zero_right w) (Commute.zero_right w)
    (Commute.one_right w)
end Formalism.FourierDecayAlt.P.Fr10
