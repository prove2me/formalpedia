-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:20.466836+00:00
-- url     : https://prove2.me/submissions/c1091d6f-8254-4f5a-a23d-90fbaab3e848

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ldeg_add

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
theorem _root_.solution {d d' : L → ℕ} {G G' : MvPolynomial (L × Fin r) R} (hG : HomD d G)
    (hG' : HomD d' G') : HomD (fun i => d i + d' i) (G * G') := by
  classical
  intro β hβ i
  obtain ⟨b1, h1, b2, h2, rfl⟩ := Finset.mem_add.mp (support_mul G G' hβ)
  rw [ldeg_add, hG b1 h1 i, hG' b2 h2 i]
end Formalism.MainNotions.PlaneGram
