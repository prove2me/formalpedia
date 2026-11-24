-- Prove2me | solution 1 for Formalism.REAL.indexArrayAction_mul_permutePositions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:59:04.858422+00:00
-- url     : https://prove2.me/submissions/b49f5555-2da0-4b4e-b84f-16eb9c2919a1

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_factorAction_mul_permuteFactors
import Theorems.Thm_Formalism_REAL_pointwiseAction_mul_permutePositions

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j)) (a b : Fin n) :
    arrE E j a b * permArr V n σ = permArr V n σ * arrE E j a b := by
  simp only [arrE, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, factorAction_mul_permuteFactors, pointwiseAction_mul_permutePositions]
  congr 1
  exact Equiv.sum_comp σ.symm (fun i => permArr V n σ * factorAction i a b)
end Formalism.REAL
