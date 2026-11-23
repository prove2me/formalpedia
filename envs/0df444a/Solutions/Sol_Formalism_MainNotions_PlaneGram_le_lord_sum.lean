-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.le_lord_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:27.711432+00:00
-- url     : https://prove2.me/submissions/d7b48925-5e1c-4a9c-af38-9f4b255b8e31

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {R : Type} [Semiring R]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {ι : Type} {n : WithTop ℤ} (s : Finset ι) (f : ι → LaurentPolynomial R)
    (h : ∀ i ∈ s, n ≤ lord (f i)) : n ≤ lord (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lord_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_lord_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.MainNotions.PlaneGram
