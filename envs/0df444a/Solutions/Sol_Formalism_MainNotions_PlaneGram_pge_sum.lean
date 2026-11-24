-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.pge_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:22.513056+00:00
-- url     : https://prove2.me/submissions/a4c7af64-61b0-423b-91f3-b61b561b6339

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_sum

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
theorem _root_.solution {ι : Type} {n : WithTop ℤ} (s : Finset ι)
    (f : ι → MvPolynomial σ (LaurentPolynomial R)) (h : ∀ i ∈ s, pge n (f i)) :
    pge n (∑ i ∈ s, f i) := by
  intro β; rw [coeff_sum]; exact le_lord_sum s _ fun i hi => h i hi β
end Formalism.MainNotions.PlaneGram
