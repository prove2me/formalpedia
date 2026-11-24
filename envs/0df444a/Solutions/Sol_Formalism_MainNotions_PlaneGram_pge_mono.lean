-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.pge_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:10.065912+00:00
-- url     : https://prove2.me/submissions/f7c164c4-1aef-4119-9e0d-3262ff2e6b06

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
variable {R : Type} [CommSemiring R] {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {m n : WithTop ℤ} (h : m ≤ n) {F : MvPolynomial σ (LaurentPolynomial R)}
    (hF : pge n F) : pge m F := fun β => h.trans (hF β)
end Formalism.MainNotions.PlaneGram
