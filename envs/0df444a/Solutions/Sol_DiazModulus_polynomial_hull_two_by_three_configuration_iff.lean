-- Prove2me | solution 1 for DiazModulus.polynomial_hull_two_by_three_configuration_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T14:00:06.172891+00:00
-- url     : https://prove2.me/submissions/d029b5b7-e10d-4976-9b07-1f09bbe8606e

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_polynomial_hull_no_two_by_three_configuration

open Complex ComplexConjugate

/-! # The polynomial hulls carrying a `2 × 3` configuration

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `P ∈ Q̄[X]` and `W = span_Q̄ {1, u, ū, P(u), P(u)‾}`.
A `2 × 3` configuration in `W` exists exactly when `P` has degree `2` or `3`.

If the degree is at most `1` or at least `4`, `polynomial_hull_no_two_by_three_configuration`
excludes a configuration. In degrees `2` and `3` there are explicit ones; throughout `ū = ρ/u`.
* Degree `2`: `u² ∈ W`, since `P(u) − p₁u − p₀ = p₂u²`. The products of `(1, u)` and `(ū, 1, u)`
  are `ū, 1, u, ρ, u, u²`.
* Degree `3`: with `c = p₂/p₃` and `Q = u³ + cu²`, both `Q ≡ P(u)/p₃` modulo `Q̄ + Q̄u` and
  `Q̄ ≡ P(u)‾/p̄₃` modulo `Q̄ + Q̄ū` lie in `W`. The products of `(1, u²)` and `(ū, u + c, Q̄)` are
  `ū, u + c, Q̄, ρu, Q` and `u²Q̄ = ρ²ū + c̄ρ²`.

Freeness: multiplied by `u` (degree `2`) or `u³` (degree `3`), a relation among the second family
becomes a polynomial identity of degree at most `4` at the transcendental `u`; its coefficients
are, up to the non-zero factor `ρ`, the coefficients of the relation.
-/

namespace R16_hullIff

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- A polynomial relation of degree `4` over `Q̄` at `u ∉ Q̄` is trivial. -/
theorem five_terms {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ a₃ a₄ : ↥Qbar}
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 + C a₄ * X ^ 4)
    (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; exact h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ) a from rfl,
    Polynomial.aeval_algHom_apply, hp, map_zero]

/-- The conjugate of an algebraic number, as an element of `Q̄`. -/
noncomputable def cq (a : ↥Qbar) : ↥Qbar := ⟨conj (a : ℂ), conj_mem_Qbar a.2⟩

/-- Membership in `W` from an explicit combination of its five generators. -/
theorem mem_W {u t z zc w : ℂ} (c₁ c₂ c₃ c₄ c₅ : ↥Qbar)
    (h : w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc) :
    w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ) := by
  have hs : ∀ v ∈ ({1, u, t, z, zc} : Set ℂ), ∀ c : ↥Qbar,
      (c : ℂ) * v ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ) := fun v hv c => by
    rw [← smul_eq_mul, ← Subfield.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span hv)
  rw [h]
  refine add_mem (add_mem (add_mem (add_mem ?_ (hs u (by simp) c₂)) (hs t (by simp) c₃))
    (hs z (by simp) c₄)) (hs zc (by simp) c₅)
  simpa using hs 1 (by simp) c₁

theorem config_of {W : Submodule (↥Qbar) ℂ} {x₀ x₁ y₀ y₁ y₂ : ℂ}
    (h00 : x₀ * y₀ ∈ W) (h01 : x₀ * y₁ ∈ W) (h02 : x₀ * y₂ ∈ W) (h10 : x₁ * y₀ ∈ W)
    (h11 : x₁ * y₁ ∈ W) (h12 : x₁ * y₂ ∈ W) : ∀ i j, ![x₀, x₁] i * ![y₀, y₁, y₂] j ∈ W := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

/-- `(1, uᵏ)` is free for `k = 1, 2`. -/
theorem li_one_pow {u : ℂ} (hu : u ∉ Qbar) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    LinearIndependent (↥Qbar) ![1, u ^ k] := by
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  simp only [Subfield.smul_def] at hst
  rcases hk with rfl | rfl
  · obtain ⟨h0, h1, -⟩ := five_terms hu (a₀ := s) (a₁ := t) (a₂ := 0) (a₃ := 0) (a₄ := 0)
      (by push_cast; linear_combination hst)
    exact ⟨h0, h1⟩
  · obtain ⟨h0, -, h2, -⟩ := five_terms hu (a₀ := s) (a₁ := 0) (a₂ := t) (a₃ := 0) (a₄ := 0)
      (by push_cast; linear_combination hst)
    exact ⟨h0, h2⟩

theorem li_three {v₀ v₁ v₂ : ℂ}
    (h : ∀ g₀ g₁ g₂ : ↥Qbar, (g₀ : ℂ) * v₀ + g₁ * v₁ + g₂ * v₂ = 0 → g₀ = 0 ∧ g₁ = 0 ∧ g₂ = 0) :
    LinearIndependent (↥Qbar) ![v₀, v₁, v₂] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Subfield.smul_def] at hg
  obtain ⟨h0, h1, h2⟩ := h (g 0) (g 1) (g 2) (by simpa using hg)
  intro i
  fin_cases i
  exacts [h0, h1, h2]

/-- Degree two: the configuration `(1, u) ⊗ (ū, 1, u)`. -/
theorem deg_two {u : ℂ} (hu : u ∉ Qbar) {σ p₀ p₁ p₂ q : ↥Qbar} (hσ : σ ≠ 0)
    (hcu : conj u * u = σ) (hq : (q : ℂ) * p₂ = 1) {A : ℂ}
    (hA : A = (p₀ : ℂ) + p₁ * u + p₂ * u ^ 2) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈
        Submodule.span Qbar ({1, u, conj u, A, conj A} : Set ℂ) := by
  refine ⟨![1, u], ![conj u, 1, u], by simpa using li_one_pow hu (k := 1) (by simp),
    li_three fun g₀ g₁ g₂ hg => ?_, config_of ?_ ?_ ?_ ?_ ?_ ?_⟩
  · obtain ⟨e₀, e₁, e₂, -⟩ := five_terms hu (a₀ := g₀ * σ) (a₁ := g₁) (a₂ := g₂) (a₃ := 0)
      (a₄ := 0) (by push_cast; linear_combination u * hg - g₀ * hcu)
    exact ⟨(mul_eq_zero.1 e₀).resolve_right hσ, e₁, e₂⟩
  · exact mem_W 0 0 1 0 0 (by push_cast; ring)
  · exact mem_W 1 0 0 0 0 (by push_cast; ring)
  · exact mem_W 0 1 0 0 0 (by push_cast; ring)
  · exact mem_W σ 0 0 0 0 (by push_cast; linear_combination hcu)
  · exact mem_W 0 1 0 0 0 (by push_cast; ring)
  · exact mem_W (-(q * p₀)) (-(q * p₁)) 0 q 0
      (by push_cast; linear_combination (-(q : ℂ)) * hA - u ^ 2 * hq)

/-- Degree three: the configuration `(1, u²) ⊗ (ū, u + c, ū³ + c̄ū²)`. -/
theorem deg_three {u : ℂ} (hu : u ∉ Qbar) {σ p₀ p₁ p₂ p₃ q : ↥Qbar} (hσ : σ ≠ 0)
    (hcu : conj u * u = σ) (hq : (q : ℂ) * p₃ = 1) {A : ℂ}
    (hA : A = (p₀ : ℂ) + p₁ * u + p₂ * u ^ 2 + p₃ * u ^ 3) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈
        Submodule.span Qbar ({1, u, conj u, A, conj A} : Set ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c : ↥Qbar, (c : ℂ) = q * p₂ := ⟨q * p₂, rfl⟩
  have hA' : conj A = (cq p₀ : ℂ) + cq p₁ * conj u + cq p₂ * conj u ^ 2 + cq p₃ * conj u ^ 3 := by
    rw [hA]; simp only [map_add, map_mul, map_pow]; rfl
  have hq' : (cq q : ℂ) * cq p₃ = 1 := by
    simp only [cq]; rw [← map_mul, hq, map_one]
  have hc' : (cq c : ℂ) = cq q * cq p₂ := by simp only [cq]; rw [hc, map_mul]
  refine ⟨![1, u ^ 2], ![conj u, u + c, conj u ^ 3 + cq c * conj u ^ 2],
    li_one_pow hu (k := 2) (by simp), li_three fun g₀ g₁ g₂ hg => ?_, config_of ?_ ?_ ?_ ?_ ?_ ?_⟩
  · obtain ⟨e₀, -, e₂, -, e₄⟩ := five_terms hu (a₀ := g₂ * σ ^ 3) (a₁ := g₂ * cq c * σ ^ 2)
      (a₂ := g₀ * σ) (a₃ := g₁ * c) (a₄ := g₁) (by
        push_cast
        linear_combination u ^ 3 * hg - (g₀ * u ^ 2 + g₂ * ((conj u * u) ^ 2 + conj u * u * σ +
          σ ^ 2) + g₂ * cq c * u * (conj u * u + σ)) * hcu)
    exact ⟨(mul_eq_zero.1 e₂).resolve_right hσ, e₄,
      (mul_eq_zero.1 e₀).resolve_right (pow_ne_zero 3 hσ)⟩
  · exact mem_W 0 0 1 0 0 (by push_cast; ring)
  · exact mem_W c 1 0 0 0 (by push_cast; ring)
  · exact mem_W (-(cq q * cq p₀)) 0 (-(cq q * cq p₁)) 0 (cq q)
      (by push_cast; rw [hc']; linear_combination (-(cq q : ℂ)) * hA' - conj u ^ 3 * hq')
  · exact mem_W 0 σ 0 0 0 (by push_cast; linear_combination u * hcu)
  · exact mem_W (-(q * p₀)) (-(q * p₁)) 0 q 0
      (by push_cast; linear_combination (-(q : ℂ)) * hA - u ^ 3 * hq + u ^ 2 * hc)
  · exact mem_W (cq c * σ ^ 2) 0 (σ ^ 2) 0 0 (by
      push_cast
      linear_combination (conj u + cq c) * (conj u * u + σ) * hcu)

end R16_hullIff

open DiazModulus R16_hullIff Polynomial in
theorem solution {u : ℂ} (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u)) (P : (↥Qbar)[X]) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈
        Submodule.span Qbar ({1, u, conj u, aeval u P, conj (aeval u P)} : Set ℂ)) ↔
      (P.natDegree = 2 ∨ P.natDegree = 3) := by
  constructor
  · intro h
    by_contra hne
    exact polynomial_hull_no_two_by_three_configuration hu hρ P (by omega) h
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  set σ : ↥Qbar := ⟨u * conj u, mem_Qbar_iff.2 hρ⟩
  have hσ : σ ≠ 0 := fun h =>
    mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) (congrArg Subtype.val h)
  have hcu : conj u * u = σ := mul_comm _ _
  have hlead : ∀ n, P.natDegree = n → n ≠ 0 → (↑(P.coeff n)⁻¹ : ℂ) * P.coeff n = 1 := by
    intro n hn h0
    have hP : P ≠ 0 := by rintro rfl; rw [natDegree_zero] at hn; omega
    have hc : P.coeff n ≠ 0 := hn ▸ leadingCoeff_ne_zero.2 hP
    rw [← Subfield.coe_mul, inv_mul_cancel₀ hc]; rfl
  rintro (h2 | h3)
  · exact deg_two hu (p₀ := P.coeff 0) (p₁ := P.coeff 1) hσ hcu (hlead 2 h2 (by norm_num))
      (by rw [aeval_eq_sum_range, h2]; simp [Finset.sum_range_succ, Subfield.smul_def])
  · exact deg_three hu (p₀ := P.coeff 0) (p₁ := P.coeff 1) (p₂ := P.coeff 2) hσ hcu
      (hlead 3 h3 (by norm_num))
      (by rw [aeval_eq_sum_range, h3]; simp [Finset.sum_range_succ, Subfield.smul_def])
