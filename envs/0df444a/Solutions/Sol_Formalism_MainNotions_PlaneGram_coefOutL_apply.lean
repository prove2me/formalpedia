-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coefOutL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:18:13.073822+00:00
-- url     : https://prove2.me/submissions/03a40b95-4e39-49e8-870e-2f987a4a0260

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
theorem _root_.solution (μ : L × Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K) :
    coefOutL out μ F = coefOut out μ F := rfl
end Formalism.MainNotions.PlaneGram
