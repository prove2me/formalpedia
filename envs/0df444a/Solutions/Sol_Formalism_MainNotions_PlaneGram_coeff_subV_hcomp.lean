-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_subV_hcomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:27.424802+00:00
-- url     : https://prove2.me/submissions/50140981-6f0e-454a-8c93-b7d08c3411b2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_substS_monomial__39ec68064bef
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS_monomial_eq_zero

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
    (substS ι sg S A B (hcomp d F)).coeff β =
      if (∀ i, ldeg β i = d i) then (substS ι sg S A B F).coeff β else 0 := by
  have hexp : (substS ι sg S A B (hcomp d F)).coeff β =
      ∑ α ∈ F.support, if (∀ i, ldeg α i = d i) then
        ι (F.coeff α) * (substS ι sg S A B (monomial α 1)).coeff β else 0 := by
    unfold hcomp
    rw [map_sum, coeff_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs
    · rw [substS_monomial', coeff_C_mul]
    · rw [map_zero, coeff_zero]
  rw [hexp]
  split_ifs with hβ
  · rw [coeff_substS]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs with hα
    · rfl
    · rw [coeff_substS_monomial_eq_zero, mul_zero]
      intro h; exact hα fun i => (h i).symm.trans (hβ i)
  · refine Finset.sum_eq_zero fun α _ => ?_
    split_ifs with hα
    · rw [coeff_substS_monomial_eq_zero, mul_zero]
      intro h; exact hβ fun i => (h i).trans (hα i)
    · rfl
end Formalism.MainNotions.PlaneGram
