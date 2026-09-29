-- Prove2me | solution 1 for Diaz.conj_mem_hull
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:11.160902+00:00
-- url     : https://prove2.me/submissions/05ebe17b-c44d-40da-870e-3ef1d117b3d2

import Mathlib
import Definitions.Def_Diaz_Closure

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

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

theorem mem_hull_of_mem_base {z : ℂ} (hz : z ∈ K) : z ∈ hull K u :=
  Subfield.subset_closure (Or.inl hz)
end

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

theorem self_mem_hull : u ∈ hull K u :=
  Subfield.subset_closure (Or.inr rfl)
end

end Diaz

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

open Diaz in
theorem solution (hK : ∀ z ∈ K, conj z ∈ K) (hu : u ≠ 0)
    (hrho : u * conj u ∈ K) :
    ∀ z ∈ hull K u, conj z ∈ hull K u := by
  intro z hz
  induction hz using Subfield.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact mem_hull_of_mem_base (hK x hx)
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [← conj_eq_rho_div hu]
        exact div_mem (mem_hull_of_mem_base hrho) self_mem_hull
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
end
