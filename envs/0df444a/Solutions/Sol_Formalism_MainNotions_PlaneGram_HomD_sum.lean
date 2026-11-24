-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:25.83581+00:00
-- url     : https://prove2.me/submissions/f2173278-aee9-40a9-882e-1cb5090252e2

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
theorem _root_.solution {ι : Type} {d : L → ℕ} (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) R)
    (h : ∀ k ∈ s, HomD d (f k)) : HomD d (∑ k ∈ s, f k) := by
  classical
  intro β hβ i
  obtain ⟨k, hk, hkβ⟩ := Finset.mem_biUnion.mp (support_sum hβ)
  exact h k hk β hkβ i
end Formalism.MainNotions.PlaneGram
