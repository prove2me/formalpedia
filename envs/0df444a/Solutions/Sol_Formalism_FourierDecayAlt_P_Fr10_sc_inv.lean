-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.sc_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:07.248038+00:00
-- url     : https://prove2.me/submissions/775009e5-4349-4942-8df3-2d0304eb7922

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_one

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
theorem _root_.solution {α β : ℂ} (h : α * β = 1) :
    (!![α • 1, 0; 0, 1] * !![β • 1, 0; 0, 1] : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  rw [diag_mul, ← diag_one]
  simp [smul_smul, mul_comm β α, h]
end Formalism.FourierDecayAlt.P.Fr10
