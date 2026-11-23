-- Prove2me | solution 1 for Formalism.REAL.firstPositionSlice_pointwiseAction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:10:41.519572+00:00
-- url     : https://prove2.me/submissions/990cc290-a697-4233-8f95-acb355c250d0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_indexArray_ext
import Theorems.Thm_Formalism_REAL_pointwiseAction_apply
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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (α' : Fin j → Fin n × Fin n) (c d : Fin n)
    (F : Arr V n (j+1)) : sliceLin V n α' (ptE E c d F) = ptE E c d (sliceLin V n α' F) := by
  refine indexArray_ext fun β => ?_
  simp [firstPositionSlice_apply, pointwiseAction_apply]
end Formalism.REAL
