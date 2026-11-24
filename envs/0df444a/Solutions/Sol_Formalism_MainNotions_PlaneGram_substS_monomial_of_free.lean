-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.substS_monomial_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:24.662883+00:00
-- url     : https://prove2.me/submissions/d57e34f4-08fc-4630-8ee1-773b4b6db173

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_monomial

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α : L × Fin r →₀ ℕ) (c : K) (h : ∀ x ∈ α.support, x.1 ∉ S) :
    substS ι sg S A B (monomial α c) = monomial α (ι c) := by
  rw [substS_monomial]
  have : (α.prod fun x k => subX sg S A B x ^ k) = α.prod fun x k => (X x : MvPolynomial (L × Fin r) R) ^ k := by
    refine Finset.prod_congr rfl fun x hx => ?_
    simp only [subX, if_neg (h x hx)]
  rw [this, monomial_eq]
end Formalism.MainNotions.PlaneGram
