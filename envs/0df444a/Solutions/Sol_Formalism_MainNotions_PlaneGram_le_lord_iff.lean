-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.le_lord_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:28.116803+00:00
-- url     : https://prove2.me/submissions/89d95674-d11d-4e0c-92b2-be457ed9addd

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

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
theorem _root_.solution (n : WithTop ℤ) (f : LaurentPolynomial R) :
    n ≤ lord f ↔ ∀ k : ℤ, f.coeff k ≠ 0 → n ≤ (k : WithTop ℤ) := by
  unfold lord
  rw [Finset.le_min_iff]
  simp only [Finsupp.mem_support_iff]
end Formalism.MainNotions.PlaneGram
