-- Prove2me | solution 1 for Formalism.Q3.CMRootsOfUnity.no_prime_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:07.150373+00:00
-- url     : https://prove2.me/submissions/db79b205-bea1-46ad-9210-bade2a6b5635

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_gal_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMRootsOfUnity
variable {q : Fin 3 → ℕ}
variable {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}
namespace Formalism.Q3.CMRootsOfUnity
theorem _root_.solution (hH : HostGalois) (hq : Hyp3 q) (hα : IsHost q α) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (η : E) (hη : IsPrimitiveRoot η p) : False := by
  obtain ⟨hGal, _, _, _⟩ := hH q hq E α hα
  have := hGal
  have hpos := hp.pos
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hη2 : IsPrimitiveRoot (η ^ 2) p := hη.pow_of_coprime 2 hcop
  have hmin : minpoly ℚ (η ^ 2) = minpoly ℚ η := by
    rw [← cyclotomic_eq_minpoly_rat hη hpos, ← cyclotomic_eq_minpoly_rat hη2 hpos]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := E)).1 hmin
  have hσ' : σ η = η ^ 2 := hσ
  have hsq := gal_sq hH hq hα σ
  have h4 : η = η ^ 4 := by
    calc η = (σ * σ) η := by rw [hsq]; rfl
    _ = σ (σ η) := rfl
    _ = η ^ 4 := by rw [hσ', map_pow, hσ', ← pow_mul]
  have h3 : η ^ 3 = 1 := by
    have hne : η ≠ 0 := hη.ne_zero hp.ne_zero
    apply mul_left_cancel₀ hne
    linear_combination -h4
  have h5 := (hη.pow_eq_one_iff_dvd 3).1 h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h5)
end Formalism.Q3.CMRootsOfUnity
