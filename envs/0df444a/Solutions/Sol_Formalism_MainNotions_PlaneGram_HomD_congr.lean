-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:18.586055+00:00
-- url     : https://prove2.me/submissions/53cf04ac-19a6-4685-8cfe-e3aa5f04abc9

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
variable {L : Type} {r : ℕ}
variable {R : Type} [CommSemiring R]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {d d' : L → ℕ} (h : ∀ i, d i = d' i) {G : MvPolynomial (L × Fin r) R}
    (hG : HomD d G) : HomD d' G := fun β hβ i => (hG β hβ i).trans (h i)
end Formalism.MainNotions.PlaneGram
