-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.comm_lit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:50.417422+00:00
-- url     : https://prove2.me/submissions/069b0222-193a-4b84-96bb-ff5bd6f7ba5c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData

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
theorem _root_.solution {w p q r s : SlopeTestRemainingChoices S A} (hp : Commute w p) (hq : Commute w q) (hr : Commute w r)
    (hs : Commute w s) : ∀ i j, Commute w ((!![p, q; r, s] : M2 (SlopeTestRemainingChoices S A)) i j) := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [hp, hq, hr, hs]
end Formalism.FourierDecayAlt.P.Fr10
