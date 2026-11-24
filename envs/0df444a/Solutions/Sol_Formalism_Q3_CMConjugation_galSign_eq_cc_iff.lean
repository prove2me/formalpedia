-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.galSign_eq_cc_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:28:04.086986+00:00
-- url     : https://prove2.me/submissions/8e33d76b-9d36-47a7-9cad-6010541efbaf

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
import Theorems.Thm_Formalism_Q3_CMConjugation_alpha_ne_zero
import Theorems.Thm_Formalism_Q3_CMConjugation_sigma_alpha

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMConjugation
variable {q : Fin 3 → ℕ} {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}
namespace Formalism.Q3.CMConjugation
theorem _root_.solution (hq : Hyp3 q) (hα : IsHost q α) (σ : Gal(E/ℚ)) :
    galSign α σ = cc ↔ ∀ i, σ (α i) = -α i := by
  constructor
  · intro h i
    rw [sigma_alpha hα σ i, h]
    simp [cc]
  · intro h
    funext i
    unfold galSign cc
    rw [if_neg]
    rw [h i]
    intro h2
    have h3 : (2 : E) * α i = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact alpha_ne_zero hq hα i h4
end Formalism.Q3.CMConjugation
