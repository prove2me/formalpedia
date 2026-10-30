-- Prove2me | solution 1 for DiazModulus.torus_reduced_inf_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:12:30.00099+00:00
-- url     : https://prove2.me/submissions/27188bef-0b8b-43c4-a963-a6838ed890e1

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # Reduced combinations meet the torus ideal only in 0

Write a monomial of `K[X, Y, Z]` as `X^a Y^b Z^c`. Its reduced form `red m` replaces, for every
`i`, the pair `(b_i, c_i)` by `(b_i − c_i, c_i − b_i)` (truncated subtraction), and leaves the
`X`-exponents alone. It is reduced, it fixes reduced exponents, and it is unchanged when
`b_i` and `c_i` both go up by one.

Let `ρ` be the `K`-linear map `monomial m c ↦ monomial (red m) c` (`AddMonoidAlgebra.mapDomainLinearMap`). The
last property says `ρ (q · Y_i Z_i) = ρ q` for every `q` (check it on monomials), hence
`ρ (q · (Y_i Z_i − 1)) = 0`, and `ρ` vanishes on the torus ideal
(`Finsupp.mem_ideal_span_range_iff_exists_finsupp`). On a combination of reduced monomials `ρ`
is the identity (`MvPolynomial.as_sum`). So a reduced combination in the ideal equals its
image under `ρ`, which is `0`. The argument is purely combinatorial: K is any field. -/

namespace C11_T3
open DiazModulus MvPolynomial

variable {A₀ A₁ : Type*}

/-- The `Y`/`Z` partner exponent that `red` subtracts (none for the `X` variables). -/
def partner (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (v : A₀ ⊕ (A₁ × Bool)) : ℕ :=
  Sum.elim (fun _ => 0) (fun q : A₁ × Bool => m (Sum.inr (q.1, !q.2))) v

/-- The reduced form of an exponent: `(a, b, c) ↦ (a, b − c, c − b)`. -/
noncomputable def red (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) : A₀ ⊕ (A₁ × Bool) →₀ ℕ :=
  Finsupp.ofSupportFinite (fun v => m v - partner m v)
    (m.support.finite_toSet.subset fun v hv => by
      simp only [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff] at hv ⊢
      intro h0
      exact hv (by rw [h0, Nat.zero_sub]))

theorem red_apply (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (v : A₀ ⊕ (A₁ × Bool)) :
    red m v = m v - partner m v := rfl

theorem red_eq_self {m : A₀ ⊕ (A₁ × Bool) →₀ ℕ} (hm : m ∈ torusReduced A₀ A₁) : red m = m := by
  ext v
  rcases v with h | ⟨i, b⟩
  · simp [red_apply, partner]
  · have := hm i
    cases b <;> simp only [red_apply, partner, Sum.elim_inr, Bool.not_true, Bool.not_false] <;>
      omega

theorem red_add_pair (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (i : A₁) :
    red (m + Finsupp.single (Sum.inr (i, true)) 1 + Finsupp.single (Sum.inr (i, false)) 1)
      = red m := by
  classical
  ext v
  rcases v with h | ⟨j, b⟩
  · simp [red_apply, partner]
  · by_cases hj : j = i
    · subst hj
      cases b <;> simp [red_apply, partner, Finsupp.single_apply]
    · simp [red_apply, partner, Finsupp.single_apply, Ne.symm hj]

/-- The reduction map `monomial m c ↦ monomial (red m) c`. -/
noncomputable def rho (K : Type*) [Field K] :
    MvPolynomial (A₀ ⊕ (A₁ × Bool)) K →ₗ[K] MvPolynomial (A₀ ⊕ (A₁ × Bool)) K :=
  AddMonoidAlgebra.mapDomainLinearMap K K red

theorem rho_monomial (K : Type*) [Field K] (m : A₀ ⊕ (A₁ × Bool) →₀ ℕ) (c : K) :
    rho K (monomial m c) = monomial (red m) c :=
  AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

theorem rho_mul_pair (K : Type*) [Field K] (i : A₁) (q : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :
    rho K (q * (X (Sum.inr (i, true)) * X (Sum.inr (i, false)))) = rho K q := by
  induction q using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [X, X, ← mul_assoc, monomial_mul, monomial_mul, mul_one, mul_one, rho_monomial,
      rho_monomial, red_add_pair]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq]

theorem rho_eq_zero_of_mem (K : Type*) [Field K] {p : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K}
    (hp : p ∈ torusIdeal K A₀ A₁) : rho K p = 0 := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hp
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_sub, mul_one, map_sub, rho_mul_pair, sub_self]

theorem rho_eq_self (K : Type*) [Field K] {p : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K}
    (hp : p ∈ restrictSupport K (torusReduced A₀ A₁)) : rho K p = p := by
  calc rho K p = ∑ m ∈ p.support, rho K (monomial m (coeff m p)) := by
        rw [← map_sum, ← p.as_sum]
    _ = ∑ m ∈ p.support, monomial m (coeff m p) :=
        Finset.sum_congr rfl fun m hm => by rw [rho_monomial, red_eq_self (hp hm)]
    _ = p := p.as_sum.symm

end C11_T3

open DiazModulus C11_T3 in
theorem solution {K A₀ A₁ : Type*} [Field K] :
    MvPolynomial.restrictSupport K (torusReduced A₀ A₁)
      ⊓ Submodule.restrictScalars K (torusIdeal K A₀ A₁) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem] at hp
  rw [← rho_eq_self K hp.1, rho_eq_zero_of_mem K hp.2]
