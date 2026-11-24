-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_substS_monomial_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:47.731012+00:00
-- url     : https://prove2.me/submissions/09e69f6b-d0f6-40cb-8297-895541d3ee0b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_substS_monomial

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
variable {K : Type} [Field K] [DecidableEq L] {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α β : L × Fin r →₀ ℕ) (h : ¬ ∀ i, ldeg β i = ldeg α i) :
    (substS ι sg S A B (monomial α 1)).coeff β = 0 := by
  by_contra hne
  exact h (HomD_substS_monomial ι sg S A B α β (mem_support_iff.mpr hne))
end Formalism.MainNotions.PlaneGram
