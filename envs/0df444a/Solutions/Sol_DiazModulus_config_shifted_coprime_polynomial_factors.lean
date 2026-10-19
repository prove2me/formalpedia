-- Prove2me | solution 1 for DiazModulus.config_shifted_coprime_polynomial_factors
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:24.22131+00:00
-- url     : https://prove2.me/submissions/1760f0a6-210b-4fe8-93a1-16ebf8c8a48b

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rank_one_polynomial_matrix_factor

open Complex ComplexConjugate

/-! # A configuration in a shifted polynomial hull factors through coprime polynomials

Let `u ∉ Q̄`, `Hull` a `Q̄`-subspace of `Q̄[X]`, and `x ⊗ y` a `2 × 3` configuration with
`uᴺ xᵢ yⱼ = Qᵢⱼ(u)` for some `Qᵢⱼ ∈ Hull`. As `u` is transcendental over `Q̄`, evaluation at `u`
is injective on `Q̄[X]`.
* Every `Qᵢⱼ` is non-zero: its value `uᴺ xᵢ yⱼ` is non-zero, since `u ≠ 0` and free families have
  no zero entry.
* The `2 × 2` minors `Qᵢⱼ Qᵢ'ⱼ' − Qᵢⱼ' Qᵢ'ⱼ` vanish at `u` (both products are `u²ᴺ xᵢ xᵢ' yⱼ yⱼ'`),
  hence vanish.
* `rank_one_polynomial_matrix_factor` gives `Qᵢⱼ = aᵢ bⱼ` with `a₀, a₁` coprime, so `aᵢ bⱼ ∈ Hull`.
* `bⱼ(u) = (uᴺ x₀ / a₀(u)) yⱼ` is a non-zero multiple of the free family `y`, so `b` is free.
* `x₁ a₀(u) b₀(u) = uᴺ x₀ x₁ y₀ = x₀ a₁(u) b₀(u)`, and `b₀(u) ≠ 0` cancels.
-/

namespace R18_C1

open DiazModulus Polynomial

/-- `u ∉ Q̄` is transcendental over `Q̄`. -/
theorem transcendental {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem li_congr {ι : Type*} {v w : ι → ℂ} (h : LinearIndependent (↥Qbar) v)
    (e : ∀ i, v i = w i) : LinearIndependent (↥Qbar) w := by
  rwa [funext e] at h

/-- A family of polynomials whose values at `u` are a non-zero multiple of a free family. -/
theorem li_of_eval {u : ℂ} {ι : Type*} {v : ι → ℂ} {F : ι → (↥Qbar)[X]}
    (hv : LinearIndependent (↥Qbar) v) {m : ℂ} (hm : m ≠ 0) (hF : ∀ i, aeval u (F i) = m * v i) :
    LinearIndependent (↥Qbar) F := by
  have h := hv.map' (LinearMap.mulLeft (↥Qbar) m)
    (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hm))
  refine LinearIndependent.of_comp (aeval u).toLinearMap (li_congr h fun i => ?_)
  simp only [Function.comp_apply, AlgHom.toLinearMap_apply, hF, LinearMap.mulLeft_apply]

end R18_C1

open DiazModulus R18_C1 Polynomial in
theorem solution {u : ℂ} (hu : u ∉ Qbar)
    (Hull : Submodule (↥Qbar) (↥Qbar)[X]) (N : ℕ)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, ∃ Q ∈ Hull, aeval u Q = u ^ N * (x i * y j)) :
    ∃ (a : Fin 2 → (↥Qbar)[X]) (b : Fin 3 → (↥Qbar)[X]), IsCoprime (a 0) (a 1) ∧
      LinearIndependent (↥Qbar) b ∧ (∀ i j, a i * b j ∈ Hull) ∧
      x 1 * aeval u (a 0) = x 0 * aeval u (a 1) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hinj : Function.Injective (aeval (R := ↥Qbar) u) :=
    transcendental_iff_injective.1 (transcendental hu)
  choose Q hQ hQe using hxy
  have hval : ∀ i j, aeval u (Q i j) ≠ 0 := fun i j => by
    rw [hQe]
    exact mul_ne_zero (pow_ne_zero _ hu0) (mul_ne_zero (hx.ne_zero i) (hy.ne_zero j))
  have hQ0 : ∀ i j, Q i j ≠ 0 := fun i j h => hval i j (by rw [h, map_zero])
  have hminor : ∀ i i' j j', Q i j * Q i' j' = Q i j' * Q i' j := fun i i' j j' =>
    hinj (by simp only [map_mul, hQe]; ring)
  obtain ⟨a, b, hcop, hab⟩ := DiazModulus.rank_one_polynomial_matrix_factor (↥Qbar) Q hQ0 hminor
  have ha0 : aeval u (a 0) ≠ 0 := fun h => hval 0 0 (by rw [hab, map_mul, h, zero_mul])
  have hb0 : aeval u (b 0) ≠ 0 := fun h => hval 0 0 (by rw [hab, map_mul, h, mul_zero])
  refine ⟨a, b, hcop, ?_, fun i j => hab i j ▸ hQ i j, ?_⟩
  · refine li_of_eval (u := u) hy (m := u ^ N * x 0 / aeval u (a 0))
      (div_ne_zero (mul_ne_zero (pow_ne_zero _ hu0) (hx.ne_zero 0)) ha0) fun j => ?_
    have h := hQe 0 j
    rw [hab, map_mul] at h
    field_simp
    linear_combination h
  · have h0 := hQe 0 0
    have h1 := hQe 1 0
    rw [hab, map_mul] at h0 h1
    apply mul_right_cancel₀ hb0
    linear_combination x 1 * h0 - x 0 * h1
