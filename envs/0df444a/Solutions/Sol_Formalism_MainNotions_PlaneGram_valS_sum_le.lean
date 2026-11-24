-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:30.521656+00:00
-- url     : https://prove2.me/submissions/93a79214-3bc9-4598-9d49-d635c4861e28

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff_pge

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) K) (n : WithTop ℤ)
    (h : ∀ i ∈ s, n ≤ valS sg S (f i)) : n ≤ valS sg S (∑ i ∈ s, f i) := by
  rw [le_valS_iff_pge, map_sum]
  exact pge_sum s _ fun i hi => (le_valS_iff_pge sg S n _).mp (h i hi)
end Formalism.MainNotions.PlaneGram
