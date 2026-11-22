-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:35.944748+00:00
-- url     : https://prove2.me/submissions/a052dd8e-2db5-4522-99ef-adba828c3892

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, 0 ≤ v (f i)) :
    0 ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, AddValuation.map_zero]; exact le_top
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))) (AddValuation.map_add v _ _)
end Formalism.MainNotions.PlaneGram
