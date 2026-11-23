-- Prove2me | solution 1 for Formalism.REAL.firstPositionSlice_positionAction_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:58.729062+00:00
-- url     : https://prove2.me/submissions/092aa531-a857-4e85-a55b-c91e8ad212be

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_indexArray_ext
import Theorems.Thm_Formalism_REAL_factorAction_apply
import Theorems.Thm_Formalism_REAL_firstPositionSlice_apply

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
theorem _root_.solution (α' : Fin j → Fin n × Fin n) (c d : Fin n) (F : Arr V n (j+1)) :
    sliceLin V n α' (factorAction 0 c d F) = factorAction 0 c d (sliceLin V n α' F) := by
  refine indexArray_ext fun β => ?_
  simp [firstPositionSlice_apply, factorAction_apply, Fin.update_cons_zero]
end Formalism.REAL
