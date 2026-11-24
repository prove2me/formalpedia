-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.pge_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:21.494729+00:00
-- url     : https://prove2.me/submissions/5248a3af-3faa-43ed-baed-191d0c98abef

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_mul

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
theorem _root_.solution {m n : WithTop ℤ} {F G : MvPolynomial σ (LaurentPolynomial R)} (hF : pge m F)
    (hG : pge n G) : pge (m + n) (F * G) := by
  classical
  intro β; rw [coeff_mul]
  exact le_lord_sum _ _ fun x _ => le_lord_mul (hF x.1) (hG x.2)
end Formalism.MainNotions.PlaneGram
