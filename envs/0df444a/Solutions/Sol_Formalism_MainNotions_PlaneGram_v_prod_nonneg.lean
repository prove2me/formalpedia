-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_prod_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:29.444803+00:00
-- url     : https://prove2.me/submissions/0a8f468b-6d8c-439b-b7e2-c58eef79850a

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
    0 ≤ v (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, AddValuation.map_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, AddValuation.map_mul]
    exact add_nonneg (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
end Formalism.MainNotions.PlaneGram
