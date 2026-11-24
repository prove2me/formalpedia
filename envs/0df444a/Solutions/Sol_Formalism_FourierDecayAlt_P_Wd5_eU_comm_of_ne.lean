-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.eU_comm_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:10.842359+00:00
-- url     : https://prove2.me/submissions/733d38c5-796c-4de7-8d9a-d27634c904ee

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd5
theorem _root_.solution {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  have h1 : Function.update x c j a = x a := by simp [Function.update_apply, Ne.symm hc]
  have h2 : Function.update x a l c = x c := by simp [Function.update_apply, hc]
  have h3 : Function.update (Function.update x c j) a l = Function.update (Function.update x a l) c j :=
    Function.update_comm hc j l x
  rw [h1, h2, h3]
  by_cases hx : x c = i <;> by_cases hy : x a = k <;> simp [hx, hy]
end Formalism.FourierDecayAlt.P.Wd5
