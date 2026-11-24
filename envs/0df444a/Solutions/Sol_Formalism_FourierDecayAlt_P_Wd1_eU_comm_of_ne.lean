-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd1.eU_comm_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:03.904554+00:00
-- url     : https://prove2.me/submissions/658a70f4-c1ca-4276-b505-122612fa11ac

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd1
theorem _root_.solution {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  by_cases hxc : x c = i <;> by_cases hxa : x a = k <;>
    simp [Function.update_apply, hc, Ne.symm hc, hxc, hxa, Function.update_comm hc j l x]
end Formalism.FourierDecayAlt.P.Wd1
