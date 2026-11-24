-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.pge_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:36.43287+00:00
-- url     : https://prove2.me/submissions/cbda0517-025b-498f-b8d4-c9998c17ab5c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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
variable {R : Type} [CommSemiring R] {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {n : WithTop ℤ} {F G : MvPolynomial σ (LaurentPolynomial R)} (hF : pge n F)
    (hG : pge n G) : pge n (F + G) := by
  intro β; rw [coeff_add]; exact le_lord_add (hF β) (hG β)
end Formalism.MainNotions.PlaneGram
