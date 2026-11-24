-- Prove2me | solution 1 for Formalism.Q3.hostIn_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:31.151463+00:00
-- url     : https://prove2.me/submissions/359b2e98-3030-40b7-8f1d-7be4b5131d0f

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia
import Theorems.Thm_Formalism_Q3_hostIn_intCast_mem_iff
import Theorems.Thm_Formalism_Q3_hostIn_A

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
theorem _root_.solution (hG : MQGalois) (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (p : ℕ) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ))
    (hσ : ∀ x : 𝓞 E, σ • x - x ∈ P) (j : Fin 3) (hj : galSign α σ j = -1) :
    (p : ℤ) ∣ (q j : ℤ) := by
  have hne : ∀ l, (-(q l : ℤ)) ≠ 0 := fun l => by
    have := (hq.1 l).1.pos
    omega
  have hsq : α j ^ 2 = ((-(q j : ℤ) : ℤ) : E) := hα.1 j
  have hσα : σ (α j) = -α j := by
    have := (hG 3 E _ α hα hne).2.1 σ j
    rw [this, hj]
    simp
  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(q j : ℤ) = 4 * c + 1 :=
    ⟨(-(q j : ℤ) - 1) / 4, by have := (hq.1 j).2; omega⟩
  have hcE : ((-(q j : ℤ) : ℤ) : E) = 4 * c + 1 := by exact_mod_cast hc
  obtain ⟨ω, hωdef⟩ : ∃ ω : E, ω = (1 + α j) / 2 := ⟨_, rfl⟩
  have hω2 : ω ^ 2 = ω + (c : E) := by
    rw [hωdef]
    linear_combination (1 / 4 : E) * hsq + (1 / 4 : E) * hcE
  have hωint : IsIntegral ℤ ω := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X_add_C]
      norm_num
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
        Polynomial.eval₂_X_pow, hω2]
      simp
  obtain ⟨W, hWcoe⟩ : ∃ W : 𝓞 E, (W : E) = ω := ⟨⟨ω, hωint⟩, rfl⟩
  obtain ⟨A, hAcoe, hA2⟩ := hostIn_A q α hα j
  have hσW : σ • W - W = -A := by
    apply RingOfIntegers.coe_injective
    show σ (W : E) - (W : E) = -(A : E)
    rw [hWcoe, hAcoe, hωdef, map_div₀, map_add, map_one, hσα]
    have h2 : σ (2 : E) = 2 := map_ofNat σ 2
    rw [h2]
    ring
  have hAP : A ∈ P := by
    have := P.neg_mem_iff.mpr (hσW ▸ hσ W)
    simpa using this
  have hqP : ((-(q j : ℤ) : ℤ) : 𝓞 E) ∈ P := by
    rw [← hA2]
    exact P.pow_mem_of_mem hAP 2 (by norm_num)
  rw [hostIn_intCast_mem_iff p P] at hqP
  exact dvd_neg.mp hqP
end Formalism.Q3
