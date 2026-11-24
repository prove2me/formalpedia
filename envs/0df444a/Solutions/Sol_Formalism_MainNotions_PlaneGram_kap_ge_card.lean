-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.kap_ge_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:46.199247+00:00
-- url     : https://prove2.me/submissions/ad39034f-c2e5-48bc-b832-9687baed9274

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_le_kap

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {L : Type} [Fintype L] (d : L → ℕ) :
    (Fintype.card L : ℝ) * r ≤ kap p r d := le_trans (le_add_of_nonneg_left (kapL_nonneg hp r d)) (kapL_le_kap hp hr d)
end Formalism.MainNotions.PlaneGram
