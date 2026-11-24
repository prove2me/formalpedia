-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_coefOut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:42.908811+00:00
-- url     : https://prove2.me/submissions/f80dff86-8ffc-4803-b169-0bc52714153f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_eOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_eq_self_of_eOut_eq_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coefOut_monomial

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (μ β : L × Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K) :
    (coefOut out μ F).coeff β =
      if eOut out β = 0 ∧ eOut out μ = μ then F.coeff (μ + β) else 0 := by
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [coefOut_monomial]
    by_cases h1 : eOut out α = μ
    · rw [if_pos h1, coeff_monomial, coeff_monomial]
      have hμ : eOut out μ = μ := by rw [← h1, eOut_eOut]
      by_cases h2 : eIn out α = β
      · have h3 : eOut out β = 0 := by rw [← h2, eOut_eIn]
        have h4 : α = μ + β := by rw [← h1, ← h2, eOut_add_eIn]
        rw [if_pos h2, if_pos ⟨h3, hμ⟩, if_pos h4]
      · rw [if_neg h2]
        split_ifs with h3 h4
        · exfalso; apply h2
          rw [h4, eIn_add, ← hμ, eIn_eOut, zero_add, eIn_eq_self_of_eOut_eq_zero out h3.1]
        · rfl
        · rfl
    · rw [if_neg h1, coeff_zero, coeff_monomial]
      split_ifs with h3 h4
      · exfalso; apply h1
        rw [h4, eOut_add, h3.1, h3.2, add_zero]
      · rfl
      · rfl
  | add p q hp hq =>
    rw [coefOut_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp
end Formalism.MainNotions.PlaneGram
