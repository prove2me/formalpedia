-- Prove2me | solution 1 for DiazModulus.isAlgebraic_of_hyperbola_pair_not_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:57:59.045628+00:00
-- url     : https://prove2.me/submissions/29e88ab9-186f-4786-a343-81d9408974f4

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_transcendental_add_mul_add_mul_conj
import Theorems.Thm_Transcendence_isAlgebraic_adjoin_of_not_algebraicIndependent_pair

open Complex ComplexConjugate

/-! # The hyperbola step: dependent `(c₁ + u, c₂ + ū)` forces `c₁, c₂` algebraic

Let `u` be transcendental over a subfield `F` of `ℂ`, with `ρ = u ū ∈ F` (so `ρ ≠ 0`), and
`c₁, c₂ ∈ F`. By `transcendental_add_mul_add_mul_conj`, `e₁ = c₁ + u` is transcendental over `F`,
hence over `ℚ`. If `(e₁, e₂)`, `e₂ = c₂ + ū`, is algebraically dependent, then `e₂` is algebraic over
`ℚ[e₁]` (`Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair`): there are `gₖ ∈ ℚ[X]`
with `∑_{k ≤ K} gₖ(e₁) e₂ᵏ = 0` and `g_K(e₁) ≠ 0`. Evaluate at `0`: the polynomial
`R(T) = ∑ₖ gₖ(c₁ + T) (c₂ T + ρ)ᵏ T^(K−k)` has coefficients in `F` and `R(u) = u^K ∑ₖ gₖ(e₁) e₂ᵏ = 0`,
because `c₂ u + ρ = u e₂`. As `u` is transcendental over `F`, `R = 0`, so
`R(0) = g_K(c₁) ρ^K = 0`, and `c₁` is algebraic since `g_K ≠ 0`. For `c₂` the same lemma is applied
to `ū`, which is transcendental over `F` (again `transcendental_add_mul_add_mul_conj`), with
`ū · u = ρ` and the swapped pair `(c₂ + ū, c₁ + u)`. No factorisation is needed.
-/

namespace R19_F3

open Polynomial

/-- Evaluation at `0`: if `u` is transcendental over `F`, `u v = ρ ∈ F` is non-zero, `c₁, c₂ ∈ F`,
`c₁ + u` is transcendental over `ℚ` and `(c₁ + u, c₂ + v)` is dependent, then `c₁` is algebraic. -/
theorem isAlgebraic_left (F : Subfield ℂ) {u v c₁ c₂ : ℂ} (hu : Transcendental F u)
    (hρ : u * v ∈ F) (hρ0 : u * v ≠ 0) (hc₁ : c₁ ∈ F) (hc₂ : c₂ ∈ F)
    (he : Transcendental ℚ (c₁ + u))
    (hdep : ¬ AlgebraicIndependent ℚ ![c₁ + u, c₂ + v]) : IsAlgebraic ℚ c₁ := by
  obtain ⟨P, hP0, hP⟩ := Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair he hdep
  have hg : ∀ k, ∃ g : ℚ[X], aeval (c₁ + u) g = (P.coeff k : ℂ) := by
    intro k
    have hk : (P.coeff k : ℂ) ∈ (aeval (R := ℚ) (c₁ + u)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (P.coeff k).2
    obtain ⟨g, hg⟩ := hk
    exact ⟨g, hg⟩
  choose g hg using hg
  set K := P.natDegree
  have hrel : ∑ k ∈ Finset.range (K + 1), aeval (c₁ + u) (g k) * (c₂ + v) ^ k = 0 := by
    rw [aeval_eq_sum_range] at hP
    rw [← hP]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg k]
    rfl
  have hlead : aeval (c₁ + u) (g K) ≠ 0 := by
    rw [hg K]
    exact fun h0 => (leadingCoeff_ne_zero.mpr hP0) (Subtype.ext h0)
  -- the polynomial `R(T) = ∑ₖ gₖ(c₁ + T) (c₂ T + ρ)ᵏ T^(K−k)` over `F`
  let R : F[X] := ∑ k ∈ Finset.range (K + 1),
    ((g k).map (algebraMap ℚ F)).comp (C ⟨c₁, hc₁⟩ + X) *
      (C ⟨c₂, hc₂⟩ * X + C ⟨u * v, hρ⟩) ^ k * X ^ (K - k)
  have hR : ∀ x : ℂ, aeval x R = ∑ k ∈ Finset.range (K + 1),
      aeval (c₁ + x) (g k) * (c₂ * x + u * v) ^ k * x ^ (K - k) := by
    intro x
    have hcoe : ∀ y : F, algebraMap F ℂ y = y := fun _ => rfl
    simp [R, aeval_comp, aeval_map_algebraMap, hcoe]
  have hRu : aeval u R = 0 := by
    rw [hR u, ← mul_zero (u ^ K), ← hrel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : u ^ K = u ^ k * u ^ (K - k) := by rw [← pow_add, Nat.add_sub_cancel' hkK]
    rw [hpow, show c₂ * u + u * v = u * (c₂ + v) by ring, mul_pow]
    ring
  have hR0 : R = 0 := (transcendental_iff.mp hu) R hRu
  have h0 : aeval (0 : ℂ) R = aeval (c₁ + 0) (g K) * (c₂ * 0 + u * v) ^ K * 0 ^ (K - K) := by
    rw [hR 0]
    refine Finset.sum_eq_single K (fun k hk hkK => ?_) (fun h => absurd (Finset.self_mem_range_succ K) h)
    have hkK' : k < K := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkK
    rw [zero_pow (Nat.sub_ne_zero_of_lt hkK'), mul_zero]
  rw [hR0, map_zero, add_zero, mul_zero, zero_add, Nat.sub_self, pow_zero, mul_one] at h0
  have hgc : aeval c₁ (g K) = 0 :=
    (mul_eq_zero.mp h0.symm).resolve_right (pow_ne_zero _ hρ0)
  refine ⟨g K, fun hgK => hlead ?_, hgc⟩
  rw [hgK, map_zero]

end R19_F3

open DiazModulus R19_F3 in
theorem solution
    (F : Subfield ℂ) (u : ℂ) (hu : Transcendental F u) (hρ : u * conj u ∈ F)
    (c₁ c₂ : ℂ) (hc₁ : c₁ ∈ F) (hc₂ : c₂ ∈ F)
    (hdep : ¬ AlgebraicIndependent ℚ ![c₁ + u, c₂ + conj u]) :
    IsAlgebraic ℚ c₁ ∧ IsAlgebraic ℚ c₂ := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu isAlgebraic_zero
  have hρ0 : u * conj u ≠ 0 := mul_ne_zero hu0 ((map_ne_zero _).mpr hu0)
  have h1 : Transcendental F (c₁ + u) := by
    simpa using DiazModulus.transcendental_add_mul_add_mul_conj F u hu hρ c₁ 1 0 hc₁
      F.one_mem F.zero_mem (Or.inl one_ne_zero)
  have h2 : Transcendental F (c₂ + conj u) := by
    simpa using DiazModulus.transcendental_add_mul_add_mul_conj F u hu hρ c₂ 0 1 hc₂
      F.zero_mem F.one_mem (Or.inr one_ne_zero)
  have hv : Transcendental F (conj u) := by
    simpa using DiazModulus.transcendental_add_mul_add_mul_conj F u hu hρ 0 0 1 F.zero_mem
      F.zero_mem F.one_mem (Or.inr one_ne_zero)
  have hdep' : ¬ AlgebraicIndependent ℚ ![c₂ + conj u, c₁ + u] := by
    intro h
    apply hdep
    have h' := h.comp ![1, 0] (by decide)
    convert h' using 1
    funext i
    fin_cases i <;> rfl
  refine ⟨isAlgebraic_left F hu hρ hρ0 hc₁ hc₂ (h1.of_tower_top ℚ) hdep, ?_⟩
  refine isAlgebraic_left F hv (by rwa [mul_comm]) (by rwa [mul_comm]) hc₂ hc₁
    (h2.of_tower_top ℚ) ?_
  simpa using hdep'
