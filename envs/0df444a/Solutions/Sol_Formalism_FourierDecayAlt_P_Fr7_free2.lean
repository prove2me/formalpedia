-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.free2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:00.341158+00:00
-- url     : https://prove2.me/submissions/65abb02f-7fe3-4edc-9735-7a17e536b52b

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
theorem _root_.solution {p q s t : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) (hs : FreeOf a s) (ht : FreeOf a t) :
    FreeOf2 a !![p, q; s, t] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa
end Formalism.FourierDecayAlt.P.Fr7
