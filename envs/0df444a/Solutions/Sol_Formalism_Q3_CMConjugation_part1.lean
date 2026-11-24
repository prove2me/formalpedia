-- Prove2me | solution 1 for Formalism.Q3.CMConjugation.part1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:34:06.164135+00:00
-- url     : https://prove2.me/submissions/1a49004d-053a-4ccc-aa17-5332082b206c

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
import Theorems.Thm_Formalism_Q3_CMConjugation_galSign_eq_cc_iff
import Theorems.Thm_Formalism_Q3_CMConjugation_algAdjoin_eq_top
import Theorems.Thm_Formalism_Q3_CMConjugation_phi_conj

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
theorem _root_.solution (hq : Hyp3 q) (hα : IsHost q α) (φ : E →+* ℂ) (σ : Gal(E/ℚ)) :
    (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galSign α σ = cc := by
  rw [galSign_eq_cc_iff hq hα]
  constructor
  · intro h i
    apply φ.injective
    rw [h, map_neg, phi_conj hq hα]
  · intro h
    have heq : (φ.comp (σ : E →+* E)).toRatAlgHom = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top (algAdjoin_eq_top hα)
      rintro _ ⟨i, rfl⟩
      simp only [RingHom.toRatAlgHom_apply, RingHom.coe_comp, Function.comp_apply]
      change φ (σ (α i)) = starRingEnd ℂ (φ (α i))
      rw [h i, map_neg, phi_conj hq hα]
    intro x
    have := congrArg (fun f => f x) heq
    simpa using this
end Formalism.Q3.CMConjugation
