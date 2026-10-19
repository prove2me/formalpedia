-- Prove2me | solution 1 for DiazModulus.real_polynomial_hull_no_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T14:00:10.575628+00:00
-- url     : https://prove2.me/submissions/c1e59cb9-d336-4aa5-b4c6-a2bba567010a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # A real polynomial in Re u and Im u has no configuration in its hull

Let `u ∉ Q̄` with `ρ = u ū ∈ Q̄`, let `G ∈ ℝ[a, b]` have algebraic coefficients and put
`z = G(Re u, Im u)`. Write `H₀ = Q̄ + Q̄u + Q̄ū`. No `2 × 3` configuration has its products in
`span_Q̄ {1, u, ū, z, z̄}`. The proof uses Theorem B
(`circle_point_extension_two_by_three_configuration_iff`).

* `z` is real, so `z̄ = z` and the span is `H₀ + Q̄z`.
* `Re u = (u + ū)/2`, `Im u = (u − ū)/(2i)` and `ū = ρ/u`, so `z` lies in the `Q̄`-algebra of
  numbers `w` with `uᴺ w = R(u)` for some `N` and some `R ∈ Q̄[X]` (`lau`, `eval_mem`).
* As `u` is transcendental, a polynomial over `Q̄` vanishing at `u` is zero (`aeval_eq_zero`).
  Multiplying by `u²`, `c u² + d ū² ∈ H₀` forces `c = 0` (`sq_coeff`). For `w` as above and
  `α ≠ 0` algebraic, `w ∈ H₀ + Q̄(u − α)⁻¹` forces `w ∈ H₀`: multiply by `u^(N+1)(u − α)` and
  evaluate the resulting polynomial identity at `α` (`inv_case`).
* For a real `w` of that algebra outside `H₀` (`main`), Theorem B puts `w` in `H₀ + Q̄t` with
  `t = u²`, `ū²` or `(u − α)⁻¹`. If `w = c u² + h`, conjugating gives `w = c̄ ū² + h̄`, so
  `c u² − c̄ ū² ∈ H₀` and `c = 0`; the case `ū²` is symmetric; the last case is `inv_case`.
  Each puts `w` in `H₀`.
* If `z ∉ H₀`, apply this to `w = z`. If `z ∈ H₀`, the span is `H₀ ⊆ H₀ + Q̄(u² + ū²)`, and
  `u² + ū²` is real, lies in the algebra, and is outside `H₀` by the square step.
-/

namespace R16_nogo

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

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
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem_Qbar c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

theorem set_eq_insert (u w : ℂ) : ({1, u, conj u, w} : Set ℂ) = insert w {1, u, conj u} := by
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem coeffs3 {p q r w : ℂ} (hw : w ∈ Submodule.span Qbar ({p, q, r} : Set ℂ)) :
    ∃ c₁ c₂ c₃ : ↥Qbar, w = (c₁ : ℂ) * p + c₂ * q + c₃ * r := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, rfl⟩ := Submodule.mem_span_singleton.1 hw₂
  exact ⟨c₁, c₂, c₃, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

/-- `Q̄[u, u⁻¹]`: the numbers `w` with `uᴺ w ∈ Q̄[u]` for some `N`. -/
noncomputable def lau (u : ℂ) : Subalgebra (↥Qbar) ℂ where
  carrier := {w | ∃ (N : ℕ) (R : (↥Qbar)[X]), u ^ N * w = aeval u R}
  mul_mem' := by
    rintro a b ⟨N, R, hR⟩ ⟨M, S, hS⟩
    exact ⟨N + M, R * S, by rw [map_mul, ← hR, ← hS]; ring⟩
  add_mem' := by
    rintro a b ⟨N, R, hR⟩ ⟨M, S, hS⟩
    exact ⟨N + M, X ^ M * R + X ^ N * S, by
      simp only [map_add, map_mul, map_pow, aeval_X, ← hR, ← hS]; ring⟩
  algebraMap_mem' r := ⟨0, C r, by simp⟩

/-- `G(Re u, Im u)` lies in `Q̄[u, u⁻¹]`. -/
theorem eval_mem {u : ℂ} (hc : conj u ∈ lau u) (G : MvPolynomial (Fin 2) ℝ)
    (hG : ∀ s, IsAlgebraic ℚ ((G.coeff s : ℝ) : ℂ)) :
    ((MvPolynomial.eval ![u.re, u.im] G : ℝ) : ℂ) ∈ lau u := by
  have hu : u ∈ lau u := ⟨0, X, by simp⟩
  have hI : I ∈ Qbar := mem_Qbar_iff.2 ⟨X ^ 2 + C 1, X_pow_add_C_ne_zero (by norm_num) _,
    by simp⟩
  have h2 : (2 : ℂ)⁻¹ ∈ Qbar := inv_mem (ofNat_mem Qbar 2)
  have h2I : (2 * I)⁻¹ ∈ Qbar := inv_mem (mul_mem (ofNat_mem Qbar 2) hI)
  have hre : ((u.re : ℝ) : ℂ) ∈ lau u := by
    rw [Complex.re_eq_add_conj, div_eq_inv_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (⟨_, h2⟩ : ↥Qbar))
      (Subalgebra.add_mem _ hu hc)
  have him : ((u.im : ℝ) : ℂ) ∈ lau u := by
    rw [Complex.im_eq_sub_conj, div_eq_inv_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (⟨_, h2I⟩ : ↥Qbar))
      (Subalgebra.sub_mem _ hu hc)
  rw [MvPolynomial.eval_eq]
  push_cast
  refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _
    (Subalgebra.algebraMap_mem _ (⟨_, mem_Qbar_iff.2 (hG d)⟩ : ↥Qbar))
    (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
  fin_cases i
  · simpa using hre
  · simpa using him

/-- `c u² + d ū² ∈ H₀` forces `c = 0` (multiply by `u²`). -/
theorem sq_coeff {u : ℂ} (hu : u ∉ Qbar) {ρ : ↥Qbar} (hρ : u * conj u = ρ) {c d : ↥Qbar}
    (h : (c : ℂ) * u ^ 2 + d * conj u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :
    c = 0 := by
  obtain ⟨c₁, c₂, c₃, e⟩ := coeffs3 h
  have hP := aeval_eq_zero hu (P := C c * X ^ 4 + C (d * ρ ^ 2) - C c₁ * X ^ 2 - C c₂ * X ^ 3 -
    C (c₃ * ρ) * X) (by
      simp only [map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination u ^ 2 * e - ((d : ℂ) * (ρ + u * conj u) - c₃ * u) * hρ)
  simpa [coeff_X, coeff_C, coeff_X_pow, -map_mul, -map_pow] using congrArg (coeff · 4) hP

/-- In `Q̄[u, u⁻¹]`, `H₀ + Q̄(u − α)⁻¹` adds nothing to `H₀` (`α ≠ 0`). -/
theorem inv_case {u w : ℂ} (hu : u ∉ Qbar) {ρ : ↥Qbar} (hρ : u * conj u = ρ) (hw : w ∈ lau u)
    {α : ↥Qbar} (hα : α ≠ 0)
    (h : w ∈ Submodule.span Qbar ({1, u, conj u, (u - α)⁻¹} : Set ℂ)) :
    w ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
  obtain ⟨N, R, hR⟩ := hw
  rw [set_eq_insert] at h
  obtain ⟨c, h', hh', rfl⟩ := Submodule.mem_span_insert.1 h
  obtain ⟨c₁, c₂, c₃, e⟩ := coeffs3 hh'
  have hut : (u - α) * (u - α)⁻¹ = 1 :=
    mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (e ▸ α.2))
  have hP := aeval_eq_zero hu (P := X * (X - C α) * R - C c * X ^ (N + 1) -
    X ^ (N + 1) * (X - C α) * (C c₁ + C c₂ * X) - X ^ N * (X - C α) * C (c₃ * ρ)) (by
      simp only [map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X, am]
      simp only [Subfield.smul_def, smul_eq_mul] at hR
      linear_combination (-u * (u - α)) * hR + c * u ^ (N + 1) * hut + (u - α) * u ^ (N + 1) * e
        + c₃ * u ^ N * (u - α) * hρ)
  have hc : c = 0 := by
    simpa [hα] using congrArg (eval α) hP
  rw [hc, zero_smul, zero_add]
  exact hh'

/-- A real `w ∈ Q̄[u, u⁻¹]` outside `H₀`: no configuration in `H₀ + Q̄w` (Theorem B). -/
theorem main {u w : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (hw : conj w = w)
    (hA : w ∈ lau u) (hw0 : w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  intro hc
  set ρ : ↥Qbar := ⟨u * conj u, mem_Qbar_iff.2 hρ⟩
  have hρ' : u * conj u = ρ := rfl
  rcases (DiazModulus.circle_point_extension_two_by_three_configuration_iff u w hu hρ hw0).1
    hc with h | h | ⟨a, ha, ha0, h⟩
  · rw [set_eq_insert] at h
    obtain ⟨c, h', hh', e⟩ := Submodule.mem_span_insert.1 h
    have e' := congrArg conj e
    simp only [Subfield.smul_def, smul_eq_mul, map_add, map_mul, map_pow, hw] at e e'
    have := sq_coeff hu hρ' (c := c) (d := ⟨-conj (c : ℂ), neg_mem (conj_mem_Qbar c.2)⟩)
      (span_mem_of_eq (by push_cast; linear_combination e' - e)
        (Submodule.sub_mem _ (H₀_conj hh') hh'))
    exact hw0 (by rw [e, this]; simpa using hh')
  · rw [set_eq_insert] at h
    obtain ⟨c, h', hh', e⟩ := Submodule.mem_span_insert.1 h
    have e' := congrArg conj e
    simp only [Subfield.smul_def, smul_eq_mul, map_add, map_mul, map_pow, conj_conj, hw] at e e'
    have := sq_coeff hu hρ' (c := ⟨conj (c : ℂ), conj_mem_Qbar c.2⟩) (d := -c)
      (span_mem_of_eq (by push_cast; linear_combination e - e')
        (Submodule.sub_mem _ hh' (H₀_conj hh')))
    have hc : c = 0 := Subtype.ext (by simpa using congrArg Subtype.val this)
    exact hw0 (by rw [e, hc]; simpa using hh')
  · exact hw0 (inv_case hu hρ' hA (α := ⟨a, ha⟩) (fun h0 => ha0 (congrArg Subtype.val h0)) h)

end R16_nogo

open DiazModulus R16_nogo in
theorem solution {u : ℂ} (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u)) (G : MvPolynomial (Fin 2) ℝ)
    (hG : ∀ s, IsAlgebraic ℚ ((G.coeff s : ℝ) : ℂ)) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈
        Submodule.span Qbar ({1, u, conj u, ((MvPolynomial.eval ![u.re, u.im] G : ℝ) : ℂ),
          conj ((MvPolynomial.eval ![u.re, u.im] G : ℝ) : ℂ)} : Set ℂ) := by
  rintro ⟨x, y, hx, hy, hxy⟩
  set ρ : ↥Qbar := ⟨u * conj u, mem_Qbar_iff.2 hρ⟩
  have hρ' : u * conj u = ρ := rfl
  have huA : u ∈ lau u := ⟨0, Polynomial.X, by simp⟩
  have hcA : conj u ∈ lau u := ⟨1, Polynomial.C ρ, by simp [am, hρ']⟩
  have hzA := eval_mem hcA G hG
  set z := ((MvPolynomial.eval ![u.re, u.im] G : ℝ) : ℂ) with hzdef
  have hz : conj z = z := Complex.conj_ofReal _
  rw [hz, Set.pair_eq_singleton] at hxy
  by_cases hz0 : z ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)
  · refine main hu hρ (w := u ^ 2 + conj u ^ 2) (by simp [add_comm])
      (Subalgebra.add_mem _ (Subalgebra.pow_mem _ huA 2) (Subalgebra.pow_mem _ hcA 2))
      (fun h => one_ne_zero (sq_coeff hu hρ' (c := 1) (d := 1) (by simpa using h)))
      ⟨x, y, hx, hy, fun i j => ?_⟩
    have := hxy i j
    rw [set_eq_insert, Submodule.span_insert_eq_span hz0] at this
    rw [set_eq_insert]
    exact Submodule.span_mono (Set.subset_insert _ _) this
  · exact main hu hρ hz hzA hz0 ⟨x, y, hx, hy, hxy⟩
