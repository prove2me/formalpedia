-- Prove2me | solution 1 for Formalism.REAL.firstPositionSlice_positionMixedCasimir_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:56.203334+00:00
-- url     : https://prove2.me/submissions/5afd6553-7968-4f54-8430-530754b66b30

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (α' : Fin j → Fin n × Fin n) (F : Arr V n (j+1)) :
    sliceLin V n α' (OmS ε E 0 F) = OmS ε E 0 (sliceLin V n α' F) := by
  first
    | simp only [OmS, LinearMap.sum_apply, map_sum]
    | simp only [OmS, LinearMap.coe_sum, Finset.sum_apply, map_sum]
    | simp only [OmS, LinearMap.coe_fn_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · change sliceLin V n α' (factorAction 0 c d (ptE E d c F)) = factorAction 0 c d (ptE E d c (sliceLin V n α' F))
    rw [firstPositionSlice_positionAction_zero, firstPositionSlice_pointwiseAction]
  · simp
end Formalism.REAL
