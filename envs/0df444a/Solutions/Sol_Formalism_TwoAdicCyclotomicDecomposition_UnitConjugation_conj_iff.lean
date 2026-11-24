-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:03:52.583066+00:00
-- url     : https://prove2.me/submissions/71af7afb-5ae1-4a1d-8b79-ef73754e340b

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_conj_eq_inv_of_pow_eq_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_phi_conj
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_sgn_eq_neg_one_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_autToPow_eq_neg_one_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_galMap_eq_JJ_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_algAdjoin_eq_top

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
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
variable {n q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
theorem _root_.solution (hq : 0 < q) (hd : 0 < d) (h : IsLayer n q d ζ a b) (φ : L →+* ℂ)
    (σ : Gal(L/ℚ)) :
    (∀ x : L, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n := by
  obtain ⟨hζ, ha, hb, _⟩ := h
  have hφζ : (φ ζ) ^ (2 ^ n) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hconj : starRingEnd ℂ (φ ζ) = φ (ζ⁻¹) := by
    rw [map_inv₀, conj_eq_inv_of_pow_eq_one (pow_ne_zero n two_ne_zero) hφζ]
  rw [galMap_eq_JJ_iff, autToPow_eq_neg_one_iff, sgn_eq_neg_one_iff hq ha,
    sgn_eq_neg_one_iff hd hb]
  constructor
  · intro hx
    refine ⟨φ.injective ?_, φ.injective ?_, φ.injective ?_⟩
    · rw [hx, hconj]
    · rw [hx, map_neg, phi_conj hq ha]
    · rw [hx, map_neg, phi_conj hd hb]
  · rintro ⟨h1, h2, h3⟩
    have heq : (φ.comp (σ : L →+* L)).toRatAlgHom = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top (algAdjoin_eq_top ⟨hζ, ha, hb, ‹_›⟩)
      intro x hx
      simp only [RingHom.toRatAlgHom_apply, RingHom.coe_comp, Function.comp_apply]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      change φ (σ x) = starRingEnd ℂ (φ x)
      rcases hx with rfl | rfl | rfl
      · rw [h1, hconj]
      · rw [h2, map_neg, phi_conj hq ha]
      · rw [h3, map_neg, phi_conj hd hb]
    intro x
    have := congrArg (fun f => f x) heq
    simpa using this
end Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
