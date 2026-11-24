-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:22.697929+00:00
-- url     : https://prove2.me/submissions/661c3caf-44d3-48cb-ab77-b4a30467fa08

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ldeg_zero

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
theorem _root_.solution : HomD (fun _ => 0) (1 : MvPolynomial (L × Fin r) R) := by
  classical
  intro β hβ i
  have : β = 0 := by
    have := support_monomial_subset (R := R) (s := (0 : L × Fin r →₀ ℕ)) (a := 1) hβ
    simpa using this
  rw [this, ldeg_zero]
end Formalism.MainNotions.PlaneGram
