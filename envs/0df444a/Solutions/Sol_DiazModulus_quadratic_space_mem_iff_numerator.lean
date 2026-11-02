-- Prove2me | solution 1 for DiazModulus.quadratic_space_mem_iff_numerator
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:33:24.434533+00:00
-- url     : https://prove2.me/submissions/e2215279-4de6-41d7-af36-23f3544b9ab4

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Membership in the two-orbit and cyclic spans, over a common denominator

Both spans have the shape `span(1, u, u⁻¹, g, h)` with `g · u D(u) = G(u)` and `h · u D(u) = H(u)`
for a non-zero polynomial `D` (`D = P Q`, resp. `D = P²`). Then
`c₀ + c₁ u + c₂ u⁻¹ + a₁ g + a₂ h`, multiplied by `u D(u)`, is `(D A + a₁ G + a₂ H)(u)` with
`A = c₂ + c₀ X + c₁ X²`; conversely every `A` of degree `≤ 2` arises this way. -/

namespace R21b_M

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

theorem u_ne_zero {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)

theorem span5 {u g h f : ℂ} : f ∈ Submodule.span Qbar ({1, u, u⁻¹, g, h} : Set ℂ) ↔
    ∃ c₀ c₁ c₂ a₁ a₂ : ↥Qbar, f = c₀ + c₁ * u + c₂ * u⁻¹ + a₁ * g + a₂ * h := by
  simp only [Submodule.mem_span_insert, Submodule.mem_span_singleton, smul_def']
  constructor
  · rintro ⟨c₀, _, ⟨c₁, _, ⟨c₂, _, ⟨a₁, _, ⟨a₂, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨c₀, c₁, c₂, a₁, a₂, by ring⟩
  · rintro ⟨c₀, c₁, c₂, a₁, a₂, rfl⟩
    exact ⟨c₀, _, ⟨c₁, _, ⟨c₂, _, ⟨a₁, _, ⟨a₂, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by ring⟩

theorem quad_eval (u : ℂ) {A : (↥Qbar)[X]} (hA : A.natDegree ≤ 2) :
    aeval u A = (A.coeff 0 : ℂ) + (A.coeff 1 : ℂ) * u + (A.coeff 2 : ℂ) * u ^ 2 := by
  rw [aeval_eq_sum_range' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_def']
  ring

/-- The common shape of both parts. -/
theorem mem_iff_gen {u : ℂ} (hu : u ∉ Qbar) (D G H : (↥Qbar)[X]) (hD : aeval u D ≠ 0) {g h : ℂ}
    (hg : g * (u * aeval u D) = aeval u G) (hh : h * (u * aeval u D) = aeval u H) (f : ℂ) :
    f ∈ Submodule.span Qbar ({1, u, u⁻¹, g, h} : Set ℂ) ↔ ∃ (A : (↥Qbar)[X]) (a₁ a₂ : ↥Qbar),
      A.natDegree ≤ 2 ∧ f * (u * aeval u D) = aeval u (D * A + C a₁ * G + C a₂ * H) := by
  have hu0 := u_ne_zero hu
  rw [span5]
  constructor
  · rintro ⟨c₀, c₁, c₂, a₁, a₂, rfl⟩
    refine ⟨C c₂ + C c₀ * X + C c₁ * X ^ 2, a₁, a₂, by compute_degree!, ?_⟩
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]
    rw [← hg, ← hh]
    field_simp
    ring
  · rintro ⟨A, a₁, a₂, hA, he⟩
    refine ⟨A.coeff 1, A.coeff 2, A.coeff 0, a₁, a₂, mul_right_cancel₀ (mul_ne_zero hu0 hD) ?_⟩
    rw [he]
    simp only [map_add, map_mul, aeval_C, am, quad_eval u hA]
    rw [← hg, ← hh]
    field_simp
    ring

end R21b_M

open DiazModulus R21b_M in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∀ f : ℂ, f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) ↔
      ∃ (A : (↥Qbar)[X]) (a₁ a₂ : ↥Qbar), A.natDegree ≤ 2 ∧
        f * (u * aeval u P * aeval u Q) = aeval u (P * Q * A + C a₁ * (Q ^ 2 * S₁) + C a₂ * (P ^ 2 * S₂))) ∧
    (∀ f : ℂ, f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) ↔
      ∃ (A : (↥Qbar)[X]) (a₁ a₂ : ↥Qbar), A.natDegree ≤ 2 ∧
        f * (u * aeval u P ^ 2) = aeval u (P ^ 2 * A + C a₁ * (P * Q * S₁) + C a₂ * (Q * (Q * S₁ + P * S₂)))) := by
  have hu0 := u_ne_zero hu
  have tr : Transcendental (↥Qbar) u := by
    have : Algebra.IsAlgebraic ℚ Qbar :=
      ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
    exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')
  have hPu : aeval u P ≠ 0 := fun h => hP (transcendental_iff.1 tr P h)
  have hQu : aeval u Q ≠ 0 := fun h => hQ (transcendental_iff.1 tr Q h)
  refine ⟨fun f => ?_, fun f => ?_⟩
  · have := mem_iff_gen hu (P * Q) (Q ^ 2 * S₁) (P ^ 2 * S₂) (by simp [hPu, hQu])
      (g := aeval u Q * aeval u S₁ / (u * aeval u P)) (h := aeval u P * aeval u S₂ / (u * aeval u Q))
      (by simp only [map_mul, map_pow]; field_simp) (by simp only [map_mul, map_pow]; field_simp) f
    simpa only [map_mul, mul_assoc] using this
  · have := mem_iff_gen hu (P ^ 2) (P * Q * S₁) (Q * (Q * S₁ + P * S₂)) (by simp [hPu])
      (g := aeval u Q * aeval u S₁ / (u * aeval u P))
      (h := aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2))
      (by simp only [map_mul, map_pow]; field_simp) (by simp only [map_mul, map_pow, map_add]; field_simp) f
    simpa only [map_pow] using this
