-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.comm2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:51.945748+00:00
-- url     : https://prove2.me/submissions/144db10d-9407-4cc4-b0bc-debb1c664d0c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {a : S}
namespace Formalism.FourierDecayAlt.P.Fr7
theorem _root_.solution {b p q s t : SlopeTestRemainingChoices S A} (hp : Commute b p) (hq : Commute b q) (hs : Commute b s) (ht : Commute b t) :
    ∀ i j, Commute b ((!![p, q; s, t] : M2 (SlopeTestRemainingChoices S A)) i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa
end Formalism.FourierDecayAlt.P.Fr7
