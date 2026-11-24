-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.kapL_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:39.60805+00:00
-- url     : https://prove2.me/submissions/be2d70ad-4a71-4ed3-afbc-db49679d9f1f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_term_nonneg

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {L : Type} [Fintype L] (d : L → ℕ) :
    0 ≤ kapL p r d := Finset.sum_nonneg fun i _ => kapL_term_nonneg hp r (d i)
end Formalism.MainNotions.PlaneGram
