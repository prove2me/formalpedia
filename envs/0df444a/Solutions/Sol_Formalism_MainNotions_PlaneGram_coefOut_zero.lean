-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coefOut_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:19:01.745733+00:00
-- url     : https://prove2.me/submissions/ee6d052f-9666-47f9-8f7d-d290ca86fa6e

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
theorem _root_.solution (μ : L × Fin r →₀ ℕ) :
    coefOut out μ (0 : MvPolynomial (L × Fin r) K) = 0 := by
  simp [coefOut]
end Formalism.MainNotions.PlaneGram
