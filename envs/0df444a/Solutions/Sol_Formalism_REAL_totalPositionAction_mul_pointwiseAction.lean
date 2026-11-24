-- Prove2me | solution 1 for Formalism.REAL.totalPositionAction_mul_pointwiseAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:43:49.249573+00:00
-- url     : https://prove2.me/submissions/6e7f8a68-ab84-42fe-903b-c959adc3caae

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_factorAction_mul_pointwiseAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (a b c d : Fin n) :
    positionsE V n j a b * ptE E c d = ptE E c d * positionsE V n j a b := by
  simp only [positionsE, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => factorAction_mul_pointwiseAction E i a b c d
end Formalism.REAL
