-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.sum_hcomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:25.484064+00:00
-- url     : https://prove2.me/submissions/0eb067fc-4f3e-4870-9df1-50f1bcb9e458

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_hcomp

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
theorem _root_.solution (F : MvPolynomial (L × Fin r) K) :
    F = ∑ d ∈ F.support.image (fun α i => ldeg α i), hcomp d F := by
  ext β
  rw [coeff_sum]
  simp only [coeff_hcomp]
  by_cases hβ : β ∈ F.support
  · rw [Finset.sum_eq_single (fun i => ldeg β i)]
    · rw [if_pos fun i => rfl]
    · intro d _ hd
      rw [if_neg]
      intro h; exact hd (funext fun i => (h i).symm)
    · intro h; exact absurd (Finset.mem_image_of_mem _ hβ) h
  · rw [notMem_support_iff.mp hβ]
    simp
end Formalism.MainNotions.PlaneGram
