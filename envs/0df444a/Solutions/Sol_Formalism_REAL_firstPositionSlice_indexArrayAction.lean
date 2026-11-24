-- Prove2me | solution 1 for Formalism.REAL.firstPositionSlice_indexArrayAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:32.221562+00:00
-- url     : https://prove2.me/submissions/5294830c-0b5e-479b-8006-273bc85c77b4

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_firstPositionSlice_positionAction_zero
import Theorems.Thm_Formalism_REAL_firstPositionSlice_pointwiseAction

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (α' : Fin j → Fin n × Fin n) (a b : Fin n)
    (F : Arr V n (j+1)) :
    sliceLin V n α' (arrE E (j+1) a b F) = arrE E 1 a b (sliceLin V n α' F) +
      ∑ k : Fin j, sliceLin V n α' (factorAction k.succ a b F) := by
  first
    | simp only [arrE, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero, firstPositionSlice_positionAction_zero, firstPositionSlice_pointwiseAction, add_zero]
    | simp only [arrE, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, map_add, map_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero, firstPositionSlice_positionAction_zero, firstPositionSlice_pointwiseAction, add_zero]
    | simp only [arrE, LinearMap.add_apply, LinearMap.coe_fn_sum, Finset.sum_apply, map_add, map_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero, firstPositionSlice_positionAction_zero, firstPositionSlice_pointwiseAction, add_zero]
  abel
end Formalism.REAL
