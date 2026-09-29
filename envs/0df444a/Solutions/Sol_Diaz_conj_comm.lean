-- Prove2me | solution 1 for Diaz.conj_comm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:27:25.051816+00:00
-- url     : https://prove2.me/submissions/8a997db4-ec32-4ea7-b15a-a2e1efe6d135

import Mathlib
import Definitions.Def_Diaz_Closure
import Theorems.Thm_Diaz_eqOn_hull

namespace Diaz

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- With `ρ = u * conj u`, the conjugate of `u` is `ρ / u`.

Trivial as algebra, and it is the entire content of the closure theorem:
`conj u` is not an independent quantity but a rational function of `u`
over the base field.  Everything else follows. -/
theorem conj_eq_rho_div (hu : u ≠ 0) : (u * conj u) / u = conj u := by
  field_simp
end

end Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u t : ℂ}

open Diaz in
theorem solution (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    (hKconj : ∀ a ∈ K, conj a ∈ K)
    (hu0 : u ≠ 0) (ht0 : t ≠ 0) (hΦu : Φ u = t)
    (hρ : u * conj u ∈ K) (hρt : t * conj t = u * conj u) :
    ∀ z ∈ hull K u, Φ (conj z) = conj (Φ z) := by
  have key : ∀ z ∈ hull K u,
      (Φ.comp (starRingEnd ℂ)) z = ((starRingEnd ℂ).comp Φ) z := by
    refine eqOn_hull _ _ ?_ ?_
    · intro a ha
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [hK _ (hKconj a ha), hK a ha]
    · simp only [RingHom.coe_comp, Function.comp_apply, hΦu]
      -- `Φ (conj u) = conj t`, both equal `ρ / t`
      have h1 : conj u = (u * conj u) / u := (conj_eq_rho_div hu0).symm
      have h2 : conj t = (u * conj u) / t := by
        rw [← hρt]; field_simp
      rw [h1, h2, map_div₀, hK _ hρ, hΦu]
  intro z hz
  simpa using key z hz
end
