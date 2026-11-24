-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_C_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:27.550052+00:00
-- url     : https://prove2.me/submissions/07b5613a-d10e-44c8-875f-a86a8c40d1a1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ldeg_single

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
theorem _root_.solution [DecidableEq L] (c : R) (i : L) (b b' : Fin r) :
    HomD (ldeg (Finsupp.single (i, b') 1)) (C c * X (i, b) : MvPolynomial (L × Fin r) R) := by
  intro β hβ j
  have hm : (C c * X (i, b) : MvPolynomial (L × Fin r) R) = monomial (Finsupp.single (i, b) 1) c := by
    rw [X, C_mul_monomial, mul_one]
  rw [hm] at hβ
  have : β = Finsupp.single (i, b) 1 := by
    have := support_monomial_subset hβ
    simpa using this
  rw [this, ldeg_single, ldeg_single]
end Formalism.MainNotions.PlaneGram
