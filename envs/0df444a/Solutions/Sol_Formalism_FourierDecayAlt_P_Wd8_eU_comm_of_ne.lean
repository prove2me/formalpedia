-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.eU_comm_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:01.583152+00:00
-- url     : https://prove2.me/submissions/1a24a286-2e1d-46d3-9c8b-a8ff570b0ce4

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  refine Matrix.ext fun x y => ?_
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply, Function.update_comm hc]
  by_cases h1 : x c = i <;> by_cases h2 : x a = k <;>
    simp [Function.update_apply, hc, Ne.symm hc, h1, h2]
end Formalism.FourierDecayAlt.P.Wd8
