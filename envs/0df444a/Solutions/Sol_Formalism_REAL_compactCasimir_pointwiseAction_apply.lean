-- Prove2me | solution 1 for Formalism.REAL.compactCasimir_pointwiseAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:09.686564+00:00
-- url     : https://prove2.me/submissions/1547a43e-dd42-4c0b-baf9-88419f5694df

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_pointwiseAction_apply
import Theorems.Thm_Formalism_REAL_indexArray_sum_apply
import Theorems.Thm_Formalism_REAL_compactCasimir_apply

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : CasK ε (ptE (j := j) E) F α = CasK ε E (F α) := by
  rw [compactCasimir_apply, compactCasimir_apply, indexArray_sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [indexArray_sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [pointwiseAction_apply, pointwiseAction_apply]
  · rfl
end Formalism.REAL
