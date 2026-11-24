-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.diagScalar_commute_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:10:47.633992+00:00
-- url     : https://prove2.me/submissions/0ff9f608-9859-4703-9c64-894055327f22

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_mul_diagScalar_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution {x : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (h : ∀ i j, Commute x (M i j)) :
    Commute (d0 x) M := by
  show d0 x * M = M * d0 x
  ext i j
  rw [diagScalar_mul_apply, mul_diagScalar_apply]
  exact congrFun (congrFun (h i j).eq _) _
end Formalism.FourierDecayAlt.P.Wd11
