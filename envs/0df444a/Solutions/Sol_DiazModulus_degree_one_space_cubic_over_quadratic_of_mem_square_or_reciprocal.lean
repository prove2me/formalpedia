-- Prove2me | solution 1 for DiazModulus.degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T09:52:01.036473+00:00
-- url     : https://prove2.me/submissions/8945f4c9-0e7f-4001-b797-fbd538ded9da

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A square or reciprocal in `span{1, u, ū, g, ug}` makes `u·g` a cubic over a quadratic

Let `u ∉ Q̄` with `ρ = u ū ∈ Q̄`, so `ρ ≠ 0` and `ū = ρ/u`. Write the given element
`t ∈ {u², ū², (u − a)⁻¹}` as `t = c₀ + c₁u + c₂ū + αg + βug` (span unpacking) and clear
denominators; with `R, N ∈ Q̄[X]` as below, `u·R(u)·g = N(u)` is a `linear_combination` of
the expansion of `t` (and of `(u − a)(u − a)⁻¹ = 1` in the third case).
* `t = u²`: `R = α + βX`, `N = X³ − c₁X² − c₀X − c₂ρ` (multiply by `u`); `N` is monic of degree `3`.
* `t = ū²`: `R = X(α + βX)`, `N = ρ² − X(c₀X + c₁X² + c₂ρ)` (multiply by `u²`); `N(0) = ρ² ≠ 0`.
* `t = (u − a)⁻¹`: `R = (X − a)(α + βX)`, `N = X − (X − a)(c₀X + c₁X² + c₂ρ)` (multiply by
  `u(u − a)`); `N(a) = a ≠ 0`.
In every case `N ≠ 0`, so `R ≠ 0`: otherwise `N(u) = 0`, and `u` is transcendental over `Q̄`
(`Q̄` is algebraic over `ℚ`, `Algebra.IsAlgebraic.transcendental_iff`). The degree bounds are
`compute_degree!`. -/

namespace R17_vis_a

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem coeffs {u z zc t w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar, w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

/-- An identity `u·R(u)·g = N(u)` with `N ≠ 0` forces `R ≠ 0`. -/
theorem pack {u g : ℂ} (hu : u ∉ Qbar) (R N : (↥Qbar)[X]) (hN : N ≠ 0)
    (hR2 : R.natDegree ≤ 2) (hN3 : N.natDegree ≤ 3) (h : u * aeval u R * g = aeval u N) :
    ∃ R N : (↥Qbar)[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧
      u * aeval u R * g = aeval u N := by
  refine ⟨R, N, ?_, hR2, hN3, h⟩
  rintro rfl
  exact hN (aeval_eq_zero hu (by rw [← h]; simp))

end R17_vis_a

open DiazModulus Polynomial R17_vis_a in
theorem solution
    (u g : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (ht : u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) ∨
        conj u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) ∨
        ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ)) :
    ∃ R N : (↥Qbar)[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧ u * aeval u R * g = aeval u N := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  obtain ⟨ρ, hρc⟩ : ∃ ρ : ↥Qbar, (ρ : ℂ) = u * conj u := ⟨⟨_, mem_Qbar_iff.2 hρ⟩, rfl⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) (by rw [← hρc]; rfl)
  rcases ht with h | h | ⟨a, ha, ha0, h⟩
  · obtain ⟨c₀, c₁, c₂, α, β, h⟩ := coeffs h
    refine pack hu (C α + C β * X) (X ^ 3 - C c₁ * X ^ 2 - C c₀ * X - C (c₂ * ρ)) ?_
      (by compute_degree!) (by compute_degree!) ?_
    · intro hN
      have := congrArg (coeff · 3) hN
      simp [coeff_X_pow] at this
    · simp only [map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X, am]
      rw [hρc]
      linear_combination (-u) * h
  · obtain ⟨c₀, c₁, c₂, α, β, h⟩ := coeffs h
    refine pack hu (X * (C α + C β * X))
      (C (ρ ^ 2) - X * (C c₀ * X + C c₁ * X ^ 2 + C (c₂ * ρ))) ?_
      (by compute_degree!) (by compute_degree!) ?_
    · intro hN
      have := congrArg (coeff · 0) hN
      simp only [coeff_sub, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, sub_zero] at this
      exact pow_ne_zero 2 hρ0 this
    · simp only [map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X, am]
      rw [hρc]
      linear_combination (-u ^ 2) * h
  · obtain ⟨a', rfl⟩ : ∃ a' : ↥Qbar, (a' : ℂ) = a := ⟨⟨a, ha⟩, rfl⟩
    have ha'0 : a' ≠ 0 := by rintro rfl; exact ha0 rfl
    have hinv : (u - a') * (u - a')⁻¹ = 1 :=
      mul_inv_cancel₀ (sub_ne_zero.2 fun h' => hu (h' ▸ a'.2))
    obtain ⟨c₀, c₁, c₂, α, β, h⟩ := coeffs h
    refine pack hu ((X - C a') * (C α + C β * X))
      (X - (X - C a') * (C c₀ * X + C c₁ * X ^ 2 + C (c₂ * ρ))) ?_
      (by compute_degree!) (by compute_degree!) ?_
    · intro hN
      have := congrArg (eval a') hN
      simp [ha'0] at this
    · simp only [map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X, am]
      rw [hρc]
      linear_combination (-(u * (u - a'))) * h + u * hinv
