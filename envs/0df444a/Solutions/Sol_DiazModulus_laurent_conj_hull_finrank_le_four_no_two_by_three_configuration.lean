-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_finrank_le_four_no_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:43:40.128389+00:00
-- url     : https://prove2.me/submissions/9e6f86fa-ff6c-4ecb-b7d8-69551489b37a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff
import Theorems.Thm_DiazModulus_polynomial_hull_no_two_by_three_configuration

open Complex ComplexConjugate

/-! # A Laurent hull of dimension at most four carries no configuration

Let `v ∉ Q̄` with `v v̄ = 1`, `z = Σ_{|j| ≤ k} c_j v^j` with `c_j ∈ Q̄`, `H₀ = span_Q̄ {1, v, v̄}` and
`W = span_Q̄ {1, v, v̄, z, z̄}` with `dim W ≤ 4`. Note `v v̄ = 1` is algebraic.
* If `z ∈ H₀`, then `z̄ ∈ H₀` too and `W ≤ H₀`, the polynomial hull of `P = 0`; Theorem C(iii)
  (`polynomial_hull_no_two_by_three_configuration`, degree `≤ 1`) excludes a configuration.
* Otherwise `1, v, v̄, z` are free (`LinearIndependent.finCons`), so `span {1, v, v̄, z}` has
  dimension `4` and equals `W`. Theorem B (`circle_point_extension_two_by_three_configuration_iff`)
  puts `z` in `H₀ + Q̄w` with `w ∈ {v², v̄², (v − a)⁻¹}`, `a ≠ 0`, with a non-zero coefficient `δ`.
  - `w = v²` or `v̄²`: `z̄ ∈ span {1, v, v̄, z}`; multiplied by `v²` this is a quartic identity at the
    transcendental `v`, whose constant (resp. top) coefficient is `δ̄`. So `δ = 0`.
  - `w = (v − a)⁻¹`: `v^k z = F(v)` for a polynomial `F`, so `X (X − a) F = (X − a) B + δ X^(k+1)`
    holds in `Q̄[X]`; at `X = a` it reads `0 = δ a^(k+1)`.
-/

namespace R18_C8

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

/-- The conjugate of an algebraic number, as an element of `Q̄`. -/
noncomputable def cq (a : ↥Qbar) : ↥Qbar := ⟨conj (a : ℂ), conj_mem_Qbar a.2⟩

theorem coeffs4 {p q r s w : ℂ} (hw : w ∈ Submodule.span Qbar ({p, q, r, s} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ : ↥Qbar, w = (c₁ : ℂ) * p + c₂ * q + c₃ * r + c₄ * s := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, rfl⟩ := Submodule.mem_span_singleton.1 hw₃
  exact ⟨c₁, c₂, c₃, c₄, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

/-- Membership in `H₀` from an explicit combination. -/
theorem mem_H₀ {u t w : ℂ} (c₁ c₂ c₃ : ↥Qbar) (h : w = (c₁ : ℂ) * 1 + c₂ * u + c₃ * t) :
    w ∈ Submodule.span Qbar ({1, u, t} : Set ℂ) := by
  have hs : ∀ x ∈ ({1, u, t} : Set ℂ), ∀ c : ↥Qbar,
      (c : ℂ) * x ∈ Submodule.span Qbar ({1, u, t} : Set ℂ) := fun x hx c => by
    rw [← smul_eq_mul, ← Subfield.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span hx)
  rw [h]
  exact add_mem (add_mem (hs 1 (by simp) c₁) (hs u (by simp) c₂)) (hs t (by simp) c₃)

/-- `H₀` is conjugation-stable. -/
theorem H₀_conj {u w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :
    conj w ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [map_one]; exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [conj_conj]; exact Submodule.subset_span (by simp)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = cq c • conj x := map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

/-- `P = Σ_{|j| ≤ k} γ_j X^{j+k}`, so that `P(x) = x^k Σ γ_j x^j`. -/
noncomputable def lpoly (k : ℕ) (γ : ℤ → ↥Qbar) : (↥Qbar)[X] :=
  ∑ j ∈ Finset.Icc (-(k : ℤ)) k, C (γ j) * X ^ (j + k).toNat

theorem lpoly_aeval (k : ℕ) (γ : ℤ → ↥Qbar) {x : ℂ} (hx : x ≠ 0) :
    aeval x (lpoly k γ) = x ^ k * ∑ j ∈ Finset.Icc (-(k : ℤ)) k, (γ j : ℂ) * x ^ j := by
  simp only [lpoly, map_sum, map_mul, aeval_C, aeval_X_pow, am, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : 0 ≤ j + k := by simp only [Finset.mem_Icc] at hj; omega
  rw [← zpow_natCast x (j + k).toNat, Int.toNat_of_nonneg hj', zpow_add₀ hx, zpow_natCast]
  ring

theorem cq_eq_zero {a : ↥Qbar} (h : cq a = 0) : a = 0 :=
  Subtype.ext ((map_eq_zero (starRingEnd ℂ)).1 (congrArg Subtype.val h : conj (a : ℂ) = 0))

/-- A non-zero `v²`-part does not survive conjugation inside `span {1, v, v̄, z}`. -/
theorem sq_case {v z : ℂ} (hv : v ∉ Qbar) (hv1 : v * conj v = 1) {a₁ a₂ a₃ δ : ↥Qbar}
    (hz : z = (a₁ : ℂ) * 1 + a₂ * v + a₃ * conj v + δ * v ^ 2)
    (hcz : conj z ∈ Submodule.span Qbar ({1, v, conj v, z} : Set ℂ)) : δ = 0 := by
  obtain ⟨b₁, b₂, b₃, b₄, hb⟩ := coeffs4 hcz
  subst hz
  have hcz' : conj ((a₁ : ℂ) * 1 + a₂ * v + a₃ * conj v + δ * v ^ 2) =
      (cq a₁ : ℂ) + cq a₃ * v + cq a₂ * conj v + cq δ * conj v ^ 2 := by
    simp only [map_add, map_mul, map_pow, map_one, conj_conj, cq]; ring
  obtain ⟨h0, -⟩ := five_terms hv (a₀ := cq δ) (a₁ := cq a₂ - b₃ - b₄ * a₃)
    (a₂ := cq a₁ - b₁ - b₄ * a₁) (a₃ := cq a₃ - b₂ - b₄ * a₂) (a₄ := -(b₄ * δ)) (by
      push_cast
      linear_combination (-v ^ 2) * (hb.symm.trans hcz') + (-(cq a₂ : ℂ) * v -
        cq δ * v * conj v - cq δ + a₃ * b₄ * v + b₃ * v) * hv1)
  exact cq_eq_zero h0

/-- A non-zero `v̄²`-part does not survive conjugation inside `span {1, v, v̄, z}`. -/
theorem csq_case {v z : ℂ} (hv : v ∉ Qbar) (hv1 : v * conj v = 1) {a₁ a₂ a₃ δ : ↥Qbar}
    (hz : z = (a₁ : ℂ) * 1 + a₂ * v + a₃ * conj v + δ * conj v ^ 2)
    (hcz : conj z ∈ Submodule.span Qbar ({1, v, conj v, z} : Set ℂ)) : δ = 0 := by
  obtain ⟨b₁, b₂, b₃, b₄, hb⟩ := coeffs4 hcz
  subst hz
  have hcz' : conj ((a₁ : ℂ) * 1 + a₂ * v + a₃ * conj v + δ * conj v ^ 2) =
      (cq a₁ : ℂ) + cq a₃ * v + cq a₂ * conj v + cq δ * v ^ 2 := by
    simp only [map_add, map_mul, map_pow, map_one, conj_conj, cq]; ring
  obtain ⟨-, -, -, -, h4⟩ := five_terms hv (a₀ := -(b₄ * δ)) (a₁ := cq a₂ - b₃ - b₄ * a₃)
    (a₂ := cq a₁ - b₁ - b₄ * a₁) (a₃ := cq a₃ - b₂ - b₄ * a₂) (a₄ := cq δ) (by
      push_cast
      linear_combination (-v ^ 2) * (hb.symm.trans hcz') + (-(cq a₂ : ℂ) * v +
        a₃ * b₄ * v + b₃ * v + b₄ * δ * v * conj v + b₄ * δ) * hv1)
  exact cq_eq_zero h4

/-- A Laurent polynomial has no pole at `a ≠ 0`: `δ = 0`. -/
theorem inv_case {v z : ℂ} (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (k : ℕ) (γ : ℤ → ↥Qbar)
    (hL : z = ∑ j ∈ Finset.Icc (-(k : ℤ)) k, (γ j : ℂ) * v ^ j) {a a₁ a₂ a₃ δ : ↥Qbar}
    (ha : a ≠ 0) (hz : z = (a₁ : ℂ) * 1 + a₂ * v + a₃ * conj v + δ * (v - a)⁻¹) : δ = 0 := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have hva : v - a ≠ 0 := fun h => hv (by rw [sub_eq_zero.1 h]; exact a.2)
  have e : (v - a) * (v - a)⁻¹ = 1 := mul_inv_cancel₀ hva
  have hF := lpoly_aeval k γ hv0
  rw [← hL] at hF
  set T : (↥Qbar)[X] := X * (X - C a) * lpoly k γ - (X - C a) * (C a₁ * X ^ (k + 1) +
    C a₂ * X ^ (k + 2) + C a₃ * X ^ k) - C δ * X ^ (k + 1) with hT
  have hT0 : T = 0 := aeval_eq_zero hv (by
    simp only [hT, map_sub, map_mul, map_add, aeval_X, aeval_C, aeval_X_pow, am, hF]
    linear_combination v * (v - a) * v ^ k * hz + a₃ * v ^ k * (v - a) * hv1 +
      δ * v ^ k * v * e)
  have h := congrArg (eval a) hT0
  simp only [hT, eval_sub, eval_mul, eval_X, eval_C, eval_add, eval_pow, sub_self, mul_zero,
    zero_mul, zero_sub, neg_eq_zero, eval_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero _ ha)

theorem set_eq_insert (u w : ℂ) : ({1, u, conj u, w} : Set ℂ) = insert w {1, u, conj u} := by
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

end R18_C8

open DiazModulus R18_C8 Polynomial in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (h4 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ)) ≤ 4) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) := by
  set z := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j with hzdef
  set W := Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ) with hW
  rintro ⟨x, y, hx, hy, hxy⟩
  have hρ : IsAlgebraic ℚ (v * conj v) := by rw [hv1]; exact isAlgebraic_one
  by_cases hzH : z ∈ Submodule.span Qbar ({1, v, conj v} : Set ℂ)
  · refine polynomial_hull_no_two_by_three_configuration hv hρ 0 (Or.inl (by simp))
      ⟨x, y, hx, hy, fun i j => ?_⟩
    have hH : Submodule.span Qbar ({1, v, conj v} : Set ℂ) ≤ Submodule.span Qbar
        ({1, v, conj v, aeval v (0 : (↥Qbar)[X]), conj (aeval v (0 : (↥Qbar)[X]))} : Set ℂ) :=
      Submodule.span_mono (by
        intro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
        tauto)
    have hWle : W ≤ Submodule.span Qbar
        ({1, v, conj v, aeval v (0 : (↥Qbar)[X]), conj (aeval v (0 : (↥Qbar)[X]))} : Set ℂ) := by
      refine Submodule.span_le.2 ?_
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
        Submodule.subset_span (by simp), hH hzH, hH (H₀_conj hzH)⟩
    exact hWle (hxy i j)
  · have hli3 : LinearIndependent (↥Qbar) ![1, v, conj v] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_three, Subfield.smul_def] at hg
      have hg' : (g 0 : ℂ) * 1 + g 1 * v + g 2 * conj v = 0 := by simpa using hg
      obtain ⟨e0, e1, e2, -⟩ := five_terms hv (a₀ := g 2) (a₁ := g 0) (a₂ := g 1) (a₃ := 0)
        (a₄ := 0) (by push_cast; linear_combination v * hg' - (g 2 : ℂ) * hv1)
      intro i
      fin_cases i
      exacts [e1, e2, e0]
    have hr3 : Set.range ![1, v, conj v] = ({1, v, conj v} : Set ℂ) := by
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
    have hli4 : LinearIndependent (↥Qbar) ![z, 1, v, conj v] :=
      LinearIndependent.finCons hli3 (by rwa [hr3])
    have hW4 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, z} : Set ℂ)) = 4 := by
      have := finrank_span_eq_card hli4
      rw [show Set.range ![z, 1, v, conj v] = ({1, v, conj v, z} : Set ℂ) by
        rw [set_eq_insert]
        simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]]
        at this
      rw [this, Fintype.card_fin]
    have hle : Submodule.span Qbar ({1, v, conj v, z} : Set ℂ) ≤ W := by
      refine Submodule.span_le.2 ?_
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
        Submodule.subset_span (by simp), Submodule.subset_span (by simp)⟩
    have : FiniteDimensional (↥Qbar) W := FiniteDimensional.span_of_finite _ (Set.toFinite _)
    have hEq : Submodule.span Qbar ({1, v, conj v, z} : Set ℂ) = W :=
      Submodule.eq_of_le_of_finrank_le hle (by omega)
    have hcz : conj z ∈ Submodule.span Qbar ({1, v, conj v, z} : Set ℂ) := by
      rw [hEq]; exact Submodule.subset_span (by simp)
    have hconf : ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
        LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, v, conj v, z} : Set ℂ) :=
      ⟨x, y, hx, hy, fun i j => by rw [hEq]; exact hxy i j⟩
    have hne : ∀ a₁ a₂ a₃ δ : ↥Qbar, ∀ t : ℂ,
        z = (a₁ : ℂ) * 1 + a₂ * v + a₃ * conj v + δ * t → δ = 0 → False := by
      intro a₁ a₂ a₃ δ t h hδ
      subst hδ
      exact hzH (mem_H₀ a₁ a₂ a₃ (by rw [h]; push_cast; ring))
    rcases (circle_point_extension_two_by_three_configuration_iff v z hv hρ hzH).1 hconf with
      h | h | ⟨a, ha, ha0, h⟩
    · obtain ⟨a₁, a₂, a₃, δ, e⟩ := coeffs4 h
      exact hne a₁ a₂ a₃ δ _ e (sq_case hv hv1 e hcz)
    · obtain ⟨a₁, a₂, a₃, δ, e⟩ := coeffs4 h
      exact hne a₁ a₂ a₃ δ _ e (csq_case hv hv1 e hcz)
    · obtain ⟨a₁, a₂, a₃, δ, e⟩ := coeffs4 h
      exact hne a₁ a₂ a₃ δ _ e (inv_case hv hv1 k (fun j => ⟨c j, hc j⟩) rfl
        (a := ⟨a, ha⟩) (fun h0 => ha0 (congrArg Subtype.val h0)) e)
