-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.freeOf2_diag_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:49.232402+00:00
-- url     : https://prove2.me/submissions/2327c79c-9e63-404c-a45d-bdaf5c69522b

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_freeOf2_of_entries

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
theorem _root_.solution (b : S) (α : ℂ) : FreeOf2 b (!![α • 1, 0; 0, 1] : M2 (SlopeTestRemainingChoices S A)) :=
  freeOf2_of_entries (free_smul _ (free_one b)) (free_zero b) (free_zero b) (free_one b)
end Formalism.FourierDecayAlt.P.Fr10
