-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_hcomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:22.732801+00:00
-- url     : https://prove2.me/submissions/1e13f183-a331-4fe5-b9b9-d750dd403ca7

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
variable {K : Type} [Field K] [DecidableEq L] {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
variable [Fintype L]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) (β : L × Fin r →₀ ℕ) :
    (hcomp d F).coeff β = if (∀ i, ldeg β i = d i) then F.coeff β else 0 := by
  unfold hcomp
  rw [coeff_sum]
  by_cases hβ : β ∈ F.support
  · rw [Finset.sum_eq_single β]
    · split_ifs
      · rw [coeff_monomial, if_pos rfl]
      · rw [coeff_zero]
    · intro α _ hne
      split_ifs
      · rw [coeff_monomial, if_neg hne]
      · rw [coeff_zero]
    · intro h; exact absurd hβ h
  · rw [notMem_support_iff.mp hβ, ite_self]
    refine Finset.sum_eq_zero fun α hα => ?_
    split_ifs
    · rw [coeff_monomial, if_neg]
      intro h; exact hβ (h ▸ hα)
    · rw [coeff_zero]
end Formalism.MainNotions.PlaneGram
