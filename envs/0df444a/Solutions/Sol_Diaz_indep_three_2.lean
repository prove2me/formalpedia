-- Prove2me | solution 2 for Diaz.indep_three
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:26:50.741633+00:00
-- url     : https://prove2.me/submissions/f23a528f-e1f9-43e9-bf67-041c67d886fe

/-
`Diaz.indep_three` is `Diaz.indep_of_algebraic_product` at `ν = ū`.

That node says: if `p` is transcendental over `K` and `p ν` is a non-zero
element of `K`, then `1`, `ν` and `p` are `K`-independent. With `p = u` and
`ν = ū` the hypothesis `p ν ∈ K ∖ {0}` is exactly `u ū ∈ K` together with
`u ≠ 0`, which transcendence supplies. So this node is the special case of that
one in which the second element is the complex conjugate of the first, and
nothing in its proof uses that.

The previous accepted proof built the quadratic `b X² + a X + c ρ` over `K` from
scratch — the same argument as in `indep_of_algebraic_product`, inline.
-/
import Mathlib
import Theorems.Thm_Diaz_indep_of_algebraic_product

open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

open Diaz in
theorem solution (hT : Transcendental K u) (hρ : u * conj u ∈ K)
    {a b c : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (h : a + b * u + c * conj u = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hT isAlgebraic_zero
  have hρ0 : u * conj u ≠ 0 := mul_ne_zero hu0 (by simpa using hu0)
  have h' : a + c * conj u + b * u = 0 := by linear_combination h
  obtain ⟨h1, h2, h3⟩ := Diaz.indep_of_algebraic_product hT hρ hρ0 ha hc hb h'
  exact ⟨h1, h3, h2⟩
