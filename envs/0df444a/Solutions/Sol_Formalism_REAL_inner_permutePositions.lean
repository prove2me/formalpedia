-- Prove2me | solution 1 for Formalism.REAL.inner_permutePositions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:55.216258+00:00
-- url     : https://prove2.me/submissions/1cb20b4e-ba7c-4aa1-baa7-6237a090df25

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_permutePositions_apply
import Theorems.Thm_Formalism_REAL_indexArray_inner

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
theorem _root_.solution (σ : Equiv.Perm (Fin j)) (F G : Arr V n j) :
    ⟪permArr V n σ F, permArr V n σ G⟫_ℂ = ⟪F, G⟫_ℂ := by
  rw [indexArray_inner, indexArray_inner]
  simp only [permutePositions_apply]
  exact Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun α => rfl)
end Formalism.REAL
