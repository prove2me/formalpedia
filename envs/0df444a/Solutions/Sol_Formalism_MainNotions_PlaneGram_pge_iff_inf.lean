-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.pge_iff_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:38.395829+00:00
-- url     : https://prove2.me/submissions/62bb8cd3-a077-439a-8877-eccde5bba5df

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_zero

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
variable {R : Type} [CommSemiring R] {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (n : WithTop ℤ) (G : MvPolynomial σ (LaurentPolynomial R)) :
    (n ≤ G.support.inf fun β => lord (G.coeff β)) ↔ pge n G := by
  rw [Finset.le_inf_iff]
  constructor
  · intro h β
    by_cases hβ : β ∈ G.support
    · exact h β hβ
    · rw [notMem_support_iff.mp hβ, lord_zero]; exact le_top
  · intro h β _; exact h β
end Formalism.MainNotions.PlaneGram
