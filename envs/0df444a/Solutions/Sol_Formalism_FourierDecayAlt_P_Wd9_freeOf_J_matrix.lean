-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.freeOf_J_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:01.448231+00:00
-- url     : https://prove2.me/submissions/7c7d7d07-5439-47bd-b666-f870c880ed85

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution (a : S) : FreeOf2 a JJ := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J] <;>
    first | exact free_zero a | exact free_one a | exact free_neg (free_one a)
end Formalism.FourierDecayAlt.P.Wd9
