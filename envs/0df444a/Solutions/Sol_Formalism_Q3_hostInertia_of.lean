-- Prove2me | solution 1 for Formalism.Q3.hostInertia_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:10.198264+00:00
-- url     : https://prove2.me/submissions/47b3aa6e-ffb7-47b3-b35b-e9925931000b

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia
import Theorems.Thm_Formalism_Q3_hostIn_card
import Theorems.Thm_Formalism_Q3_hostIn_galSign_one
import Theorems.Thm_Formalism_Q3_hostIn_key
import Theorems.Thm_Formalism_Q3_hostIn_ram_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (hH : HostGalois) (hG : MQGalois) : HostInertia := by
  intro q hq E _ _ α hα i P _ _ σ
  have hGal := hH q hq E α hα
  have : IsGalois ℚ E := hGal.1
  have hinj := hGal.2.2.1.1
  have h1 : galSign α (1 : Gal(E/ℚ)) = 1 := hostIn_galSign_one α
  have hfwd : ∀ τ : Gal(E/ℚ), (∀ x : 𝓞 E, τ • x - x ∈ P) →
      (galSign α τ = 1 ∨ galSign α τ = e3 i) := by
    intro τ hτ
    have hoth : ∀ j, j ≠ i → galSign α τ j = 1 := by
      intro j hji
      rcases Int.units_eq_one_or (galSign α τ j) with h | h
      · exact h
      · exfalso
        have hd := hostIn_key hG q hq E α hα (q i) P τ hτ j h
        have := (Nat.prime_dvd_prime_iff_eq (hq.1 i).1 (hq.1 j).1).mp (by exact_mod_cast hd)
        exact hji (hq.2 this).symm
    rcases Int.units_eq_one_or (galSign α τ i) with h | h
    · left
      funext j
      by_cases hji : j = i
      · subst hji
        simpa using h
      · rw [hoth j hji]
        rfl
    · right
      funext j
      by_cases hji : j = i
      · subst hji
        simp [e3, h]
      · simp [e3, hji, hoth j hji]
  refine ⟨hfwd σ, fun h => ?_⟩
  rcases h with h | h
  · have : σ = 1 := hinj (h.trans h1.symm)
    subst this
    intro x
    simp
  · by_contra hn
    have hbot : P.inertia Gal(E/ℚ) = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      rw [Subgroup.mem_bot]
      rcases hfwd τ hτ with h' | h'
      · exact hinj (h'.trans h1.symm)
      · have := hinj (h'.trans h.symm)
        subst this
        exact absurd hτ hn
    have : Fact (q i).Prime := ⟨(hq.1 i).1⟩
    have hc := hostIn_card E (q i) P
    rw [hbot, Subgroup.card_bot] at hc
    exact hostIn_ram_ne_one q hq E α hα i P hc.symm
end Formalism.Q3
