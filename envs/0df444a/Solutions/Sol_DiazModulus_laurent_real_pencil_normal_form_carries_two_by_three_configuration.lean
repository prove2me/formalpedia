-- Prove2me | solution 1 for DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:43:51.262401+00:00
-- url     : https://prove2.me/submissions/b6c6dd43-d0b3-417f-a92a-f7d7150f7c95

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The real pencil normal form carries a `2 × 3` configuration

Let `v ∉ Q̄` with `v v̄ = 1`, `κ ∈ Q̄` with `κ κ̄ = 1`, `G ∈ Q̄[X]` of degree `n ≥ 1`, and
`g = G(v) + κ · conj(v G(v))`. Then `(1, v)` and `(v̄, 1, g)` form a configuration in
`W = span_Q̄ {1, v, v̄, g, ḡ}`.
The products are `v̄, 1, g, v v̄ = 1, v` and `v g = κ ḡ`; the last identity uses `v v̄ = 1` and
`κ κ̄ = 1` only.
Freeness of `(1, v)` is `v ∉ Q̄`. For `(v̄, 1, g)`: conjugation commutes with evaluation once the
coefficients are conjugated (`conj_aeval`), and `v̄ = v⁻¹`, so `vⁿ · conj(G(v))` is the value at `v`
of the reflected polynomial `reflect n Gᶜ` (`Polynomial.eval₂_reflect_mul_pow`), of degree at most
`n`. Multiplying a relation `g₀ v̄ + g₁ + g₂ g = 0` by `v^(n+1)` gives a polynomial identity at the
transcendental `v`, whose coefficient at `X^(2n+1)` is `g₂ · lead(G)`. So `g₂ = 0`, and then
`g₀ + g₁ v = 0` gives `g₀ = g₁ = 0`.
-/

namespace R18_C6

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
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 ha).algHom (starRingEnd ℂ).toRatAlgHom)

/-- Complex conjugation restricted to `Q̄`. -/
noncomputable def cqh : ↥Qbar →+* ↥Qbar where
  toFun a := ⟨conj (a : ℂ), conj_mem_Qbar a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ (a : ℂ) b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ (a : ℂ) b)

/-- Conjugating a value of a polynomial conjugates the point and the coefficients. -/
theorem conj_aeval (x : ℂ) (G : (↥Qbar)[X]) : conj (aeval x G) = aeval (conj x) (G.map cqh) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  rw [show (starRingEnd ℂ).comp (algebraMap (↥Qbar) ℂ) = (algebraMap (↥Qbar) ℂ).comp cqh from
    RingHom.ext fun _ => rfl]

/-- `xᴺ H(x⁻¹)` is the value at `x` of the reflected polynomial. -/
theorem inv_aeval {x : ℂ} (hx : x ≠ 0) (N : ℕ) (H : (↥Qbar)[X]) (hH : H.natDegree ≤ N) :
    x ^ N * aeval x⁻¹ H = aeval x (reflect N H) := by
  have : Invertible x := invertibleOfNonzero hx
  have h := eval₂_reflect_mul_pow (algebraMap (↥Qbar) ℂ) x N (reflect N H)
    (natDegree_reflect_le.trans (max_le le_rfl hH))
  rw [reflect_reflect, invOf_eq_inv] at h
  rw [aeval_def, aeval_def, ← h, mul_comm]

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

end R18_C6

open DiazModulus R18_C6 Polynomial in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (κ : ℂ) (hκ : κ ∈ Qbar) (hκ1 : κ * conj κ = 1) (G : Polynomial ↥Qbar) (hG : 1 ≤ G.natDegree) :
    LinearIndependent (↥Qbar) ![1, v] ∧
      LinearIndependent (↥Qbar) ![conj v, 1, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G)] ∧
      ∀ i j, ![1, v] i * ![conj v, 1, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G)] j ∈
        Submodule.span Qbar ({1, v, conj v, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G), conj (Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G))} : Set ℂ) := by
  obtain ⟨κ, rfl⟩ : ∃ k : ↥Qbar, (k : ℂ) = κ := ⟨⟨κ, hκ⟩, rfl⟩
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have hcv : conj v = v⁻¹ := (inv_eq_of_mul_eq_one_right hv1).symm
  set n := G.natDegree with hn
  have hG0 : G ≠ 0 := by rintro rfl; simp [hn] at hG
  have hlead : G.coeff n ≠ 0 := leadingCoeff_ne_zero.2 hG0
  set Gc := G.map cqh with hGc
  have hGcn : Gc.natDegree ≤ n := natDegree_map_le
  have hrefl : aeval v (reflect n Gc) = v ^ n * conj (aeval v G) := by
    rw [← inv_aeval hv0 n Gc hGcn, conj_aeval, hcv]
  refine ⟨LinearIndependent.pair_iff.2 fun s t hst => ?_, li_three fun g₀ g₁ g₂ hg => ?_,
    config_of ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simp only [Subfield.smul_def, smul_eq_mul] at hst
    obtain ⟨h0, h1, -⟩ := five_terms hv (a₀ := s) (a₁ := t) (a₂ := 0) (a₃ := 0) (a₄ := 0)
      (by push_cast; linear_combination hst)
    exact ⟨h0, h1⟩
  · rw [map_mul] at hg
    set R : (↥Qbar)[X] := C g₀ * X ^ n + C g₁ * X ^ (n + 1) + C g₂ * (G * X ^ (n + 1)) +
      C (g₂ * κ) * reflect n Gc with hR
    have hR0 : R = 0 := aeval_eq_zero hv (by
      simp only [hR, map_add, map_mul, aeval_C, aeval_X_pow, am, hrefl]
      linear_combination v ^ (n + 1) * hg -
        ((g₀ : ℂ) * v ^ n + g₂ * κ * v ^ n * conj (aeval v G)) * hv1)
    have hz : (reflect n Gc).coeff (n + (n + 1)) = 0 := coeff_eq_zero_of_natDegree_lt
      ((natDegree_reflect_le (N := n) (p := Gc)).trans_lt (max_lt (by omega) (by omega)))
    have hc := congrArg (coeff · (n + (n + 1))) hR0
    simp only [hR, coeff_add, coeff_C_mul, coeff_mul_X_pow, coeff_X_pow, coeff_C, coeff_zero,
      if_neg (show n + (n + 1) ≠ n by omega), if_neg (show n ≠ 0 by omega), mul_zero, zero_add,
      hz, add_zero] at hc
    have h2 : g₂ = 0 := by
      have : g₂ * G.coeff n = 0 := by simpa using hc
      exact (mul_eq_zero.1 this).resolve_right hlead
    subst h2
    obtain ⟨h0, h1, -⟩ := five_terms hv (a₀ := g₀) (a₁ := g₁) (a₂ := 0) (a₃ := 0) (a₄ := 0)
      (by push_cast at hg ⊢; linear_combination v * hg - (g₀ : ℂ) * hv1)
    exact ⟨h0, h1, rfl⟩
  · exact mem_W 0 0 1 0 0 (by push_cast; ring)
  · exact mem_W 1 0 0 0 0 (by push_cast; ring)
  · exact mem_W 0 0 0 1 0 (by push_cast; ring)
  · exact mem_W 1 0 0 0 0 (by push_cast; linear_combination hv1)
  · exact mem_W 0 1 0 0 0 (by push_cast; ring)
  · refine mem_W 0 0 0 0 κ ?_
    simp only [map_add, map_mul, conj_conj]
    push_cast
    linear_combination (κ : ℂ) * conj (aeval v G) * hv1 - v * aeval v G * hκ1
