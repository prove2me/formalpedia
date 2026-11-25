-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coefOut_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:18:18.388898+00:00
-- url     : https://prove2.me/submissions/028c4f3b-c3b3-477d-b86f-45dbc0888d5c

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {ι : Type} (μ : L × Fin r →₀ ℕ) (s : Finset ι)
    (f : ι → MvPolynomial (L × Fin r) K) :
    coefOut out μ (∑ i ∈ s, f i) = ∑ i ∈ s, coefOut out μ (f i) :=
  map_sum (coefOutL out μ) f s
end Formalism.MainNotions.PlaneGram
