-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd1.eU_mul_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:03.996733+00:00
-- url     : https://prove2.me/submissions/0d24bc7e-31d3-4c77-b028-d528778e9872

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
theorem _root_.solution (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [eU_mul_apply]
  by_cases hx : x a = i <;> by_cases hjk : j = k <;> simp [hx, hjk, eU_apply, Function.update_idem]
end Formalism.FourierDecayAlt.P.Wd1
