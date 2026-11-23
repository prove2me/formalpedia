-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.le_lord_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:23.500844+00:00
-- url     : https://prove2.me/submissions/c40c5eab-6981-49d4-9ae3-922da93f07c7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_iff

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
theorem _root_.solution {n : WithTop ℤ} {f g : LaurentPolynomial R} (hf : n ≤ lord f) (hg : n ≤ lord g) :
    n ≤ lord (f + g) := by
  rw [le_lord_iff] at *
  intro k hk
  by_cases h1 : f.coeff k = 0
  · apply hg k
    intro h2
    apply hk
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h1, h2, add_zero]
  · exact hf k h1
end Formalism.MainNotions.PlaneGram
