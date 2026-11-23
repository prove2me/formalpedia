-- Prove2me | solution 1 for Formalism.REAL.inner_eq_sum_firstPositionSlice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:19.163083+00:00
-- url     : https://prove2.me/submissions/e47d3772-54e2-4103-9463-2ef982c2523e

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_firstPositionSlice_apply
import Theorems.Thm_Formalism_REAL_indexArray_inner
import Theorems.Thm_Formalism_REAL_sum_fin_cons

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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (F G : Arr V n (j+1)) :
    ⟪F, G⟫_ℂ = ∑ α' : Fin j → Fin n × Fin n, ⟪sliceLin V n α' F, sliceLin V n α' G⟫_ℂ := by
  rw [indexArray_inner, sum_fin_cons]
  simp only [indexArray_inner, firstPositionSlice_apply]
end Formalism.REAL
