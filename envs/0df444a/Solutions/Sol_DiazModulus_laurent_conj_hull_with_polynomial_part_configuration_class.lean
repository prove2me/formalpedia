-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_with_polynomial_part_configuration_class
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:43:42.741295+00:00
-- url     : https://prove2.me/submissions/0deb4575-e8ce-4dce-bb3a-5f213a1391f3

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_polynomial_hull_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # A Laurent hull containing `v² P(v)` carries a configuration only in the polynomial class

Let `v ∉ Q̄` with `v v̄ = 1`, `W = span_Q̄ {1, v, v̄, z, z̄}`, and `0 ≠ P ∈ Q̄[X]` with
`v² P(v) ∈ W`. Put `Q = X² P` and `A = Q(v) = v² P(v)`. Then `W' = span_Q̄ {1, v, v̄, A, Ā} ≤ W`,
because `W` is conjugation-stable.
`W'` has dimension `5`. A relation `a₀ + a₁ v + a₂ v̄ + a₃ A + a₄ Ā = 0`, multiplied by `v^(d+2)`
with `d = deg P`, becomes a polynomial identity at the transcendental `v`; here `v̄ = v⁻¹` and
`v^d · P̄(v⁻¹)` is the reflected polynomial (`Polynomial.eval₂_reflect_mul_pow`), of degree at most
`d`, so the coefficient of `X^(2d+4)` is `a₃ · lead(P)` and `a₃ = 0`. The conjugate relation has
`ā₄` in the place of `a₃`, so `a₄ = 0`; then `a₀ + a₁ v + a₂ v̄ = 0` is trivial.
Since `dim W ≤ 5`, `W' = W`, so the configuration lies in the polynomial hull of `Q` at `u := v`
(`u ū = 1` is algebraic). Theorem C (`polynomial_hull_two_by_three_configuration_iff`) gives
`deg Q ∈ {2, 3}`, so `P = α + β X` with `(α, β) ≠ 0`, and `α v² + β v³ = v² P(v) ∈ W`.
-/

namespace R18_C7

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

theorem cqh_coe (a : ↥Qbar) : (cqh a : ℂ) = conj (a : ℂ) := rfl

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

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem_Qbar c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

theorem li_five {v₀ v₁ v₂ v₃ v₄ : ℂ}
    (h : ∀ g₀ g₁ g₂ g₃ g₄ : ↥Qbar, (g₀ : ℂ) * v₀ + g₁ * v₁ + g₂ * v₂ + g₃ * v₃ + g₄ * v₄ = 0 →
      g₀ = 0 ∧ g₁ = 0 ∧ g₂ = 0 ∧ g₃ = 0 ∧ g₄ = 0) :
    LinearIndependent (↥Qbar) ![v₀, v₁, v₂, v₃, v₄] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_five, Subfield.smul_def] at hg
  obtain ⟨h0, h1, h2, h3, h4⟩ := h (g 0) (g 1) (g 2) (g 3) (g 4) (by simpa using hg)
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3, h4]

/-- In a relation among `1, v, v̄, v² P(v)` and its conjugate, the coefficient of `v² P(v)` is `0`. -/
theorem top {v : ℂ} (hv : v ∉ Qbar) (hv1 : v * conj v = 1) {P : (↥Qbar)[X]} (hP : P ≠ 0)
    {a₀ a₁ a₂ a₃ a₄ : ↥Qbar}
    (h : (a₀ : ℂ) + a₁ * v + a₂ * conj v + a₃ * (v ^ 2 * aeval v P) +
      a₄ * conj (v ^ 2 * aeval v P) = 0) : a₃ = 0 := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have hcv : conj v = v⁻¹ := (inv_eq_of_mul_eq_one_right hv1).symm
  set d := P.natDegree
  have hrefl : aeval v (reflect d (P.map cqh)) = v ^ d * conj (aeval v P) := by
    rw [← inv_aeval hv0 d _ natDegree_map_le, conj_aeval, hcv]
  set R : (↥Qbar)[X] := C a₀ * X ^ (d + 2) + C a₁ * X ^ (d + 3) + C a₂ * X ^ (d + 1) +
    C a₃ * (P * X ^ (d + 4)) + C a₄ * reflect d (P.map cqh) with hR
  have hR0 : R = 0 := aeval_eq_zero hv (by
    simp only [hR, map_add, map_mul, aeval_C, aeval_X_pow, am, hrefl]
    rw [map_mul, map_pow] at h
    linear_combination v ^ (d + 2) * h - ((a₂ : ℂ) * v ^ (d + 1) +
      a₄ * v ^ d * conj (aeval v P) * (v * conj v + 1)) * hv1)
  have hz : (reflect d (P.map cqh)).coeff (d + (d + 4)) = 0 := coeff_eq_zero_of_natDegree_lt
    ((natDegree_reflect_le (N := d) (p := P.map cqh)).trans_lt
      (max_lt (by omega) (natDegree_map_le.trans_lt (by omega))))
  have hc := congrArg (coeff · (d + (d + 4))) hR0
  simp only [hR, coeff_add, coeff_C_mul, coeff_mul_X_pow, coeff_X_pow, coeff_zero,
    if_neg (show d + (d + 4) ≠ d + 2 by omega), if_neg (show d + (d + 4) ≠ d + 3 by omega),
    if_neg (show d + (d + 4) ≠ d + 1 by omega), mul_zero, zero_add, hz, add_zero] at hc
  exact (mul_eq_zero.1 hc).resolve_right (leadingCoeff_ne_zero.2 hP)

end R18_C7

open DiazModulus R18_C7 Polynomial in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (z : ℂ)
    (P : Polynomial ↥Qbar) (hP : P ≠ 0) (hPW : v ^ 2 * Polynomial.aeval v P ∈ Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ))
    (hconf : ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ)) :
    ∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * v ^ 2 + β * v ^ 3 ∈ Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ) := by
  set W := Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ) with hW
  have hA : aeval v (X ^ 2 * P) = v ^ 2 * aeval v P := by simp
  set W' := Submodule.span Qbar ({1, v, conj v, aeval v (X ^ 2 * P),
    conj (aeval v (X ^ 2 * P))} : Set ℂ) with hW'
  have hconjW : ∀ w ∈ W, conj w ∈ W := span_conj_stable fun x hx => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> refine Submodule.subset_span ?_ <;> simp
  have hle : W' ≤ W := by
    rw [hW', Submodule.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, hA]
    exact ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
      Submodule.subset_span (by simp), hPW, hconjW _ hPW⟩
  have hind : LinearIndependent (↥Qbar) ![1, v, conj v, aeval v (X ^ 2 * P),
      conj (aeval v (X ^ 2 * P))] := li_five fun g₀ g₁ g₂ g₃ g₄ hg => by
    rw [hA, mul_one] at hg
    have h3 : g₃ = 0 := top hv hv1 hP hg
    have h4 : cqh g₄ = 0 := by
      refine top hv hv1 hP (a₀ := cqh g₀) (a₁ := cqh g₂) (a₂ := cqh g₁) (a₄ := cqh g₃) ?_
      have := congrArg conj hg
      simp only [map_add, map_mul, conj_conj, map_zero] at this
      simp only [cqh_coe, map_mul]
      linear_combination this
    have h4' : g₄ = 0 := (map_eq_zero_iff cqh cqh.injective).1 h4
    rw [h3, h4'] at hg
    obtain ⟨e0, e1, e2, -⟩ := five_terms hv (a₀ := g₂) (a₁ := g₀) (a₂ := g₁) (a₃ := 0) (a₄ := 0)
      (by push_cast at hg ⊢; linear_combination v * hg - (g₂ : ℂ) * hv1)
    exact ⟨e1, e2, e0, h3, h4'⟩
  have hW'5 : Module.finrank (↥Qbar) W' = 5 := by
    have := finrank_span_eq_card hind
    rw [show Set.range ![1, v, conj v, aeval v (X ^ 2 * P), conj (aeval v (X ^ 2 * P))] =
      ({1, v, conj v, aeval v (X ^ 2 * P), conj (aeval v (X ^ 2 * P))} : Set ℂ) by
        simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]]
      at this
    rw [hW', this, Fintype.card_fin]
  have hW5 : Module.finrank (↥Qbar) W ≤ 5 := by
    classical
    have := finrank_span_finset_le_card (R := ↥Qbar) ({1, v, conj v, z, conj z} : Finset ℂ)
    simp only [Finset.coe_insert, Finset.coe_singleton] at this
    exact this.trans Finset.card_le_five
  have : FiniteDimensional (↥Qbar) W := FiniteDimensional.span_of_finite _ (Set.toFinite _)
  have hWW : W' = W := Submodule.eq_of_le_of_finrank_le hle (by omega)
  obtain ⟨x, y, hx, hy, hxy⟩ := hconf
  have hdeg := (polynomial_hull_two_by_three_configuration_iff hv
    (by rw [hv1]; exact isAlgebraic_one) (X ^ 2 * P)).1
    ⟨x, y, hx, hy, fun i j => hWW ▸ hxy i j⟩
  rw [natDegree_mul (pow_ne_zero 2 X_ne_zero) hP, natDegree_X_pow] at hdeg
  have hP1 : P.natDegree ≤ 1 := by omega
  have hPe := eq_X_add_C_of_natDegree_le_one hP1
  refine ⟨P.coeff 0, P.coeff 1, (P.coeff 0).2, (P.coeff 1).2, ?_, ?_⟩
  · by_contra hc
    simp only [not_or, not_not] at hc
    apply hP
    rw [hPe, show P.coeff 1 = 0 from Subtype.ext hc.2, show P.coeff 0 = 0 from Subtype.ext hc.1]
    simp
  · convert hPW using 1
    conv_rhs => rw [hPe]
    simp only [map_add, map_mul, aeval_C, aeval_X, am]
    ring
