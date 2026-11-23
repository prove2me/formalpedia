-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.free_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:49.48934+00:00
-- url     : https://prove2.me/submissions/4d3effbe-c1c6-42b8-ae3f-7cfc1038313f

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_star_eU


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
theorem _root_.solution {c : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf c b) : FreeOf c (star b) := by
  intro i j
  have := (h j i).star_star
  rwa [star_eU] at this
end Formalism.FourierDecayAlt.P.Fr10
