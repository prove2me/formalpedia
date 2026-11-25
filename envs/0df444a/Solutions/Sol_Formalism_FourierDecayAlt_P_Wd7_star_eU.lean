-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.star_eU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:11.776583+00:00
-- url     : https://prove2.me/submissions/78906550-0fc1-4dab-9616-2a8e7e7cdeef

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_apply
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd7_eU_apply__f51f2867f050
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution [StarRing A] (a : S) (i j : Fin 2) :
    star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  ext x y
  rw [Matrix.star_apply, eU_apply, eU_apply']
  by_cases h : y a = i ∧ x = Function.update y a j <;> simp [h]
end Formalism.FourierDecayAlt.P.Wd7
