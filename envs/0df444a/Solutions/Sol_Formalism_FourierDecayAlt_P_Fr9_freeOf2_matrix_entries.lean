-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.freeOf2_matrix_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:06:53.170869+00:00
-- url     : https://prove2.me/submissions/75ded1cc-90c3-4902-b361-e59a3df9d8bc

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {b : S}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution {p q s t : SlopeTestRemainingChoices S A} (hp : FreeOf b p) (hq : FreeOf b q) (hs : FreeOf b s)
    (ht : FreeOf b t) : FreeOf2 b !![p, q; s, t] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact hp
  · exact hq
  · exact hs
  · exact ht
end Formalism.FourierDecayAlt.P.Fr9
