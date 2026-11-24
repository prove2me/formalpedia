-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ddiv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:33.458059+00:00
-- url     : https://prove2.me/submissions/f8f4a8b9-e02e-422b-a56e-761d841834ef

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_eq

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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ ι : Type} (M : σ →₀ ℕ) (s : Finset ι) (f : ι → MvPolynomial σ K) :
    ddiv M (∑ i ∈ s, f i) = ∑ i ∈ s, ddiv M (f i) := by simp only [ddiv_eq, map_sum]
end Formalism.MainNotions.PlaneGram
