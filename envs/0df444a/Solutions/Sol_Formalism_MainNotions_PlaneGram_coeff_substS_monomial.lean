-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_substS_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:42:12.898981+00:00
-- url     : https://prove2.me/submissions/16ecea76-fc99-4f13-8dd7-3676ef0ed03a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_sub_eOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS_eIn_eq_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_monomial_split

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
variable (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hout : ∀ i ∈ S, ¬ out i) (α γ : L × Fin r →₀ ℕ) :
    (substS ι sg S A B (monomial α 1)).coeff γ =
      if eOut out γ = eOut out α then (substS ι sg S A B (monomial (eIn out α) 1)).coeff (eIn out γ)
      else 0 := by
  rw [substS_monomial_split ι sg S A B out hout α, coeff_monomial_mul', one_mul]
  split_ifs with h1 h2 h2
  · rw [← h2, sub_eOut]
  · apply coeff_substS_eIn_eq_zero
    intro h0
    apply h2
    ext x
    have hx := DFunLike.congr_fun h0 x
    have hle := h1 x
    simp only [eOut_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at hx hle ⊢
    split_ifs with ho
    · simp only [if_pos ho] at hx hle
      omega
    · rfl
  · exact absurd (h2 ▸ eOut_le out γ) h1
  · rfl
end Formalism.MainNotions.PlaneGram
