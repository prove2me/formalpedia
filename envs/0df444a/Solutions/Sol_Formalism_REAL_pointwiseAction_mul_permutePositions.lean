-- Prove2me | solution 1 for Formalism.REAL.pointwiseAction_mul_permutePositions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:12.511624+00:00
-- url     : https://prove2.me/submissions/3476868b-48ed-4c71-832f-bdbe9ed6aaff

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_indexArray_ext

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j)) (c d : Fin n) :
    ptE E c d * permArr V n σ = permArr V n σ * ptE E c d := by
  refine LinearMap.ext fun F => indexArray_ext fun α => ?_
  rfl
end Formalism.REAL
