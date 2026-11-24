-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.absE_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:38.630693+00:00
-- url     : https://prove2.me/submissions/49500f16-2092-4372-890c-fc4b34b76db8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial

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
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (β : Fin r →₀ ℕ) : absE β = ∑ a, β a := by
  unfold absE
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)
end Formalism.MainNotions.PlaneGram
