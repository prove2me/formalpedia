-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.eU_mul_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:52.520838+00:00
-- url     : https://prove2.me/submissions/5f1f720d-47c7-4a94-b779-abbce30d4568

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [eU_mul_apply, eU_apply]
  by_cases hjk : j = k
  · subst hjk
    simp only [Function.update_self, Function.update_idem, true_and, if_true]
    rw [eU_apply]
    by_cases h : x a = i <;> simp [h]
  · simp [hjk]
end Formalism.FourierDecayAlt.P.Wd6
