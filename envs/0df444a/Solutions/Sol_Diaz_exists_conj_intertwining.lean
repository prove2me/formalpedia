-- Prove2me | solution 1 for Diaz.exists_conj_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:29:31.208079+00:00
-- url     : https://prove2.me/submissions/f4b3341d-e35c-47bb-ba2b-0183ce46558a

import Mathlib
import Definitions.Def_Diaz_Closure
import Theorems.Thm_Diaz_conj_comm
import Theorems.Thm_Diaz_exists_ringHom_of_transcendental

namespace Diaz

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- A transcendental element is non-zero: `0` is a root of `X`. -/
theorem transcendental_ne_zero {F : Type*} [Field F] [Algebra F ℂ] {z : ℂ}
    (h : Transcendental F z) : z ≠ 0 := by
  rintro rfl
  exact h isAlgebraic_zero
end

end Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u t : ℂ}

open Diaz in
theorem solution (hKconj : ∀ a ∈ K, conj a ∈ K)
    (hu : Transcendental (↥K) u) (ht : Transcendental (↥K) t)
    (hρ : u * conj u ∈ K) (hρt : t * conj t = u * conj u) :
    ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t
      ∧ ∀ z ∈ hull K u, Φ (conj z) = conj (Φ z) := by
  obtain ⟨Φ, hK, hΦu⟩ := exists_ringHom_of_transcendental hu ht
  exact ⟨Φ, hK, hΦu, conj_comm Φ hK hKconj (transcendental_ne_zero hu)
    (transcendental_ne_zero ht) hΦu hρ hρt⟩
end
