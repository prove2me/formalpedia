-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.pge_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:29.310582+00:00
-- url     : https://prove2.me/submissions/37b40739-6dc6-4ca0-907a-767f676a4766

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
theorem _root_.solution (n : WithTop ℤ) : pge n (0 : MvPolynomial σ (LaurentPolynomial R)) := by
  intro β; rw [coeff_zero, lord_zero]; exact le_top
end Formalism.MainNotions.PlaneGram
