-- Prove2me | solution 1 for DiazModulus.laurent_real_pencil_space_excludes_squares_and_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:34:19.044035+00:00
-- url     : https://prove2.me/submissions/0a0a9d71-b060-4a5a-8831-7dec32da2119

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A Laurent real-pencil space excludes squares and reciprocals

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `v = u/s` (transcendental), `w = v⁻¹`, so `u = sv`,
`ū = sw`. Let `k = m + 2`, `f = Σ_{|j| ≤ k} c_j v^j` with `c_k ≠ 0 ≠ c_{-k} = c̄_k`,
`g = f/(s + λu) = f/(s(1 + λv))`, `W = span_Q̄ {1, u, ū, f, g}`. The polynomial
`P = Σ_j c_j X^{j+k}` (`lpoly`) has `P(v) = v^k f`, `P(0) = c_{-k}` and `natDegree P = 2k`.
For `t = α₁ + α₂u + α₃ū + α₄f + α₅g`, multiplying by `N(v)·s v^k (1 + λv)` (`N = 1` for
`t = u², ū²`; `N = sX − b` for `t = (u − b)⁻¹`) gives a polynomial identity at the transcendental
`v`, hence in `Q̄[X]` (`clear`): `T = N·(s(1 + λX)(α₁X^k + α₂sX^{k+1} + α₃sX^{k−1}) + L·P)`
with `L = α₄s(1 + λX) + α₅`.
* Degree (`top_kill`, `compute_degree`): if `α₄ ≠ 0`, `L·N·P` has degree `1 + deg N + 2k`, the
  rest at most `k + 3` (`u²`), `k + 2` (`ū²`), `k + 3` (reciprocal). So `α₄ = 0`, for `u²` when `k ≥ 3`.
* `X = 0`: `N(0)·(α₄s + α₅)·c_{-k} = T(0)`, and `T(0) = 0` except for `ū²` at `k = 2`.
* `X = −λ̄`, for `k = 2`: `1 + λX` vanishes, so `α₅·P(−λ̄) = 0`, and `P(−λ̄) = λ̄²f(−λ̄) ≠ 0`.
In each case `α₄ = α₅ = 0`; then `t ∈ Q̄ + Q̄u + Q̄ū` is refuted by a cubic in `u` (`red_*`).
-/

namespace R14_laurentExcl

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

theorem lpoly_aeval_zero (k : ℕ) (γ : ℤ → ↥Qbar) :
    aeval (0 : ℂ) (lpoly k γ) = γ (-k) := by
  simp only [lpoly, map_sum, map_mul, aeval_C, aeval_X_pow, am]
  rw [Finset.sum_eq_single (-(k : ℤ))]
  · simp
  · intro j hj hjk
    simp only [Finset.mem_Icc] at hj
    rw [zero_pow (by omega), mul_zero]
  · exact fun h => absurd (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h

theorem lpoly_natDegree (k : ℕ) (γ : ℤ → ↥Qbar) (hk : γ k ≠ 0) :
    (lpoly k γ).natDegree = 2 * k := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_sum_le_of_forall_le
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · rw [lpoly, finsetSum_coeff, Finset.sum_eq_single (k : ℤ)]
    · rw [coeff_C_mul_X_pow, if_pos (by omega)]
      exact hk
    · intro j hj hjk
      simp only [Finset.mem_Icc] at hj
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · exact fun h => absurd (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) h

/-- A linear factor `a(1 + ℓX) + b` with `a ≠ 0` raises the degree of `N P` by one. -/
theorem top_kill {P N B : (↥Qbar)[X]} {a b ℓ : ↥Qbar} {n : ℕ} (hℓ : ℓ ≠ 0)
    (hP : P.natDegree = n) (hP0 : P ≠ 0) (hN : N ≠ 0)
    (h : (C a * (1 + C ℓ * X) + C b) * N * P = B) (hB : B.natDegree < 1 + N.natDegree + n) :
    a = 0 := by
  by_contra ha
  have hL : C a * (1 + C ℓ * X) + C b = C (a * ℓ) * X + C (a + b) := by
    simp only [map_mul, map_add]
    ring
  have hL1 : (C a * (1 + C ℓ * X) + C b).natDegree = 1 := by
    rw [hL]
    exact natDegree_linear (mul_ne_zero ha hℓ)
  have hL0 : C a * (1 + C ℓ * X) + C b ≠ 0 := fun h0 => by simp [h0] at hL1
  rw [← h, natDegree_mul (mul_ne_zero hL0 hN) hP0, natDegree_mul hL0 hN, hL1, hP] at hB
  exact lt_irrefl _ hB

/-- Clearing denominators in `t = α₁ + α₂u + α₃ū + α₄f + α₅g`. -/
theorem clear {u cu v w f g t : ℂ} (hv : v ∉ Qbar) {σ ℓ α₁ α₂ α₃ α₄ α₅ : ↥Qbar} {m : ℕ}
    {P N T : (↥Qbar)[X]}
    (hvw : v * w = 1) (hu : u = σ * v) (hcu : cu = σ * w) (hp : aeval v P = v ^ (m + 2) * f)
    (hg : g * (σ * (1 + ℓ * v)) = f) (h : t = α₁ + α₂ * u + α₃ * cu + α₄ * f + α₅ * g)
    (hT : aeval v T = aeval v N * (σ * v ^ (m + 2) * (1 + ℓ * v) * t)) :
    T = N * (C σ * (1 + C ℓ * X) * (C α₁ * X ^ (m + 2) + C (α₂ * σ) * X ^ (m + 3) +
      C (α₃ * σ) * X ^ (m + 1)) + (C (α₄ * σ) * (1 + C ℓ * X) + C α₅) * P) := by
  apply sub_eq_zero.1
  apply aeval_eq_zero hv
  simp only [map_sub, map_mul, map_add, map_one, aeval_C, aeval_X, aeval_X_pow, am, hT, hp]
  linear_combination (aeval v N) * ((σ : ℂ) * v ^ (m + 2) * (1 + ℓ * v) * h +
    (σ : ℂ) * (1 + ℓ * v) * α₂ * v ^ (m + 2) * hu + (σ : ℂ) * (1 + ℓ * v) * α₃ * v ^ (m + 2) * hcu +
    (σ : ℂ) ^ 2 * (1 + ℓ * v) * α₃ * v ^ (m + 1) * hvw + α₅ * v ^ (m + 2) * hg)

theorem red_sq {u cu : ℂ} (hu : u ∉ Qbar) {σ a₁ a₂ a₃ : ↥Qbar} (hcuu : cu * u = σ * σ)
    (h : u ^ 2 = a₁ + a₂ * u + a₃ * cu) : False := by
  have hP := aeval_eq_zero hu (P := X ^ 3 - C a₂ * X ^ 2 - C a₁ * X - C (a₃ * σ * σ))
    (by
      simp only [map_sub, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination u * h + a₃ * hcuu)
  have := congrArg (coeff · 3) hP
  simp [coeff_X_pow] at this

theorem red_csq {u cu : ℂ} (hu : u ∉ Qbar) {σ a₁ a₂ a₃ : ↥Qbar} (hσ : σ ≠ 0)
    (hcuu : cu * u = σ * σ) (h : cu ^ 2 = a₁ + a₂ * u + a₃ * cu) : False := by
  have hP := aeval_eq_zero hu
    (P := C a₂ * X ^ 3 + C a₁ * X ^ 2 + C (a₃ * σ * σ) * X - C (σ * σ * σ * σ))
    (by
      simp only [map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination (-u ^ 2) * h + (cu * u + σ * σ - a₃ * u) * hcuu)
  have := congrArg (coeff · 0) hP
  simp [coeff_X, coeff_C, coeff_X_pow, hσ] at this

theorem red_inv {u cu : ℂ} (hu : u ∉ Qbar) {σ a₁ a₂ a₃ β : ↥Qbar} (hβ : β ≠ 0)
    (hcuu : cu * u = σ * σ) (h : (u - β)⁻¹ = a₁ + a₂ * u + a₃ * cu) : False := by
  have hub : (u - β) * (u - β)⁻¹ = 1 :=
    mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (by rw [e]; exact β.2))
  have hP := aeval_eq_zero hu
    (P := (X - C β) * (C a₁ * X + C a₂ * X ^ 2 + C (a₃ * σ * σ)) - X)
    (by
      simp only [map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination (-u * (u - β)) * h + u * hub - (u - β) * a₃ * hcuu)
  have := congrArg (eval β) hP
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, sub_self, zero_mul,
    zero_sub, eval_zero, neg_eq_zero] at this
  exact hβ this

/-- The statement for abstract `ū, v, w, f, g, P`. -/
theorem main {u cu v w f g r : ℂ} (hu : u ∉ Qbar) (hv : v ∉ Qbar) {σ ℓ : ↥Qbar} (hσ : σ ≠ 0)
    (hℓ : ℓ ≠ 0) {m : ℕ} {P : (↥Qbar)[X]}
    (hvw : v * w = 1) (hu' : u = σ * v) (hcu : cu = σ * w) (hp : aeval v P = v ^ (m + 2) * f)
    (hg : g * (σ * (1 + ℓ * v)) = f) (hPdeg : P.natDegree = 2 * (m + 2))
    (hP0 : aeval (0 : ℂ) P ≠ 0) (hr : 1 + ℓ * r = 0)
    (hm : 1 ≤ m ∨ (m = 0 ∧ aeval r P ≠ 0)) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, cu, f, g} : Set ℂ) ∧
      cu ^ 2 ∉ Submodule.span Qbar ({1, u, cu, f, g} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, cu, f, g} : Set ℂ) := by
  have hPne : P ≠ 0 := by rintro rfl; simp at hP0
  have hcuu : cu * u = σ * σ := by rw [hcu, hu']; linear_combination (σ : ℂ) ^ 2 * hvw
  have red : ∀ {t : ℂ} {α₁ α₂ α₃ α₄ α₅ : ↥Qbar},
      t = α₁ + α₂ * u + α₃ * cu + α₄ * f + α₅ * g → α₄ = 0 → α₅ = 0 →
        t = α₁ + α₂ * u + α₃ * cu := by
    rintro t α₁ α₂ α₃ α₄ α₅ h rfl rfl; rw [h]; push_cast; ring
  refine ⟨fun hw => ?_, fun hw => ?_, fun b hb hb0 hw => ?_⟩
  · -- `u² = σ²v²`
    obtain ⟨α₁, α₂, α₃, α₄, α₅, h⟩ := coeffs hw
    have E := clear (N := 1) (T := C (σ ^ 3) * X ^ (m + 4) * (1 + C ℓ * X)) hv hvw hu' hcu hp hg h
      (by
        simp only [map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, am]
        rw [hu']
        ring)
    have h0 := congrArg (aeval (0 : ℂ)) E
    simp only [map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, am] at h0
    have h0' : (α₄ : ℂ) * σ + α₅ = 0 := by simpa [hP0] using h0
    have hα : α₄ = 0 ∧ α₅ = 0 := by
      rcases hm with hm | ⟨rfl, hPr⟩
      · have h4 : α₄ * σ = 0 := top_kill (a := α₄ * σ) (b := α₅) hℓ hPdeg hPne one_ne_zero
          (B := C (σ ^ 3) * X ^ (m + 4) * (1 + C ℓ * X) - 1 * (C σ * (1 + C ℓ * X) *
            (C α₁ * X ^ (m + 2) + C (α₂ * σ) * X ^ (m + 3) + C (α₃ * σ) * X ^ (m + 1))))
          (by rw [E]; ring) (by
            rw [natDegree_one]; refine lt_of_le_of_lt (b := m + 5) ?_ (by omega); compute_degree; omega)
        have h4' : α₄ = 0 := (mul_eq_zero.1 h4).resolve_right hσ
        refine ⟨h4', ?_⟩
        rw [h4'] at h0'
        simpa using h0'
      · have hrE := congrArg (aeval r) E
        simp only [map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, am, hr] at hrE
        have h5 : α₅ = 0 := by simpa [hPr] using hrE
        refine ⟨?_, h5⟩
        rw [h5] at h0'
        simpa [hσ] using h0'
    exact red_sq hu hcuu (red h hα.1 hα.2)
  · -- `ū² = σ²w²`
    obtain ⟨α₁, α₂, α₃, α₄, α₅, h⟩ := coeffs hw
    have E := clear (N := 1) (T := C (σ ^ 3) * X ^ m * (1 + C ℓ * X)) hv hvw hu' hcu hp hg h
      (by
        simp only [map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, am]
        rw [hcu]
        linear_combination (-(σ : ℂ) ^ 3 * (1 + ℓ * v) * v ^ m * (v * w + 1)) * hvw)
    have h4 : α₄ * σ = 0 := top_kill (a := α₄ * σ) (b := α₅) hℓ hPdeg hPne one_ne_zero
      (B := C (σ ^ 3) * X ^ m * (1 + C ℓ * X) - 1 * (C σ * (1 + C ℓ * X) *
        (C α₁ * X ^ (m + 2) + C (α₂ * σ) * X ^ (m + 3) + C (α₃ * σ) * X ^ (m + 1))))
      (by rw [E]; ring) (by
        rw [natDegree_one]; refine lt_of_le_of_lt (b := m + 4) ?_ (by omega); compute_degree; omega)
    have h4' : α₄ = 0 := (mul_eq_zero.1 h4).resolve_right hσ
    have h5 : α₅ = 0 := by
      rcases hm with hm | ⟨rfl, hPr⟩
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        have h0 := congrArg (aeval (0 : ℂ)) E
        simp only [map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, am] at h0
        simpa [hP0, h4'] using h0
      · have hrE := congrArg (aeval r) E
        simp only [map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, am, hr] at hrE
        simpa [hPr] using hrE
    exact red_csq hu hσ hcuu (red h h4' h5)
  · -- `(u − β)⁻¹`
    obtain ⟨β, rfl⟩ : ∃ β : ↥Qbar, (β : ℂ) = b := ⟨⟨b, hb⟩, rfl⟩
    have hβ0 : β ≠ 0 := by rintro rfl; exact hb0 rfl
    obtain ⟨α₁, α₂, α₃, α₄, α₅, h⟩ := coeffs hw
    have hub : (u - β) * (u - β)⁻¹ = 1 :=
      mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (by rw [e]; exact β.2))
    have hN1 : (C σ * X - C β).natDegree = 1 := by
      rw [natDegree_sub_C, natDegree_C_mul_X _ hσ]
    have hN0 : C σ * X - C β ≠ 0 := fun h0 => by simp [h0] at hN1
    have E := clear (N := C σ * X - C β) (T := C σ * X ^ (m + 2) * (1 + C ℓ * X)) hv hvw hu'
      hcu hp hg h
      (by
        simp only [map_sub, map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, am]
        linear_combination (σ : ℂ) * v ^ (m + 2) * (1 + ℓ * v) * ((u - β)⁻¹ * hu' - hub))
    have h4 : α₄ * σ = 0 := top_kill (a := α₄ * σ) (b := α₅) hℓ hPdeg hPne hN0
      (B := C σ * X ^ (m + 2) * (1 + C ℓ * X) - (C σ * X - C β) * (C σ * (1 + C ℓ * X) *
        (C α₁ * X ^ (m + 2) + C (α₂ * σ) * X ^ (m + 3) + C (α₃ * σ) * X ^ (m + 1))))
      (by rw [E]; ring) (by
        rw [hN1]; refine lt_of_le_of_lt (b := m + 5) ?_ (by omega); compute_degree; omega)
    have h4' : α₄ = 0 := (mul_eq_zero.1 h4).resolve_right hσ
    have h0 := congrArg (aeval (0 : ℂ)) E
    simp only [map_sub, map_mul, map_pow, map_add, map_one, aeval_C, aeval_X, am] at h0
    have h5 : α₅ = 0 := by simpa [hP0, h4', hβ0] using h0
    exact red_inv hu hβ0 hcuu (red h h4' h5)

end R14_laurentExcl

open DiazModulus R14_laurentExcl Polynomial in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (k : ℕ) (c : ℤ → ℂ)
    (hc : ∀ j, c j ∈ Qbar) (hcs : ∀ j, c (-j) = conj (c j)) (hck : c k ≠ 0)
    (hk : 3 ≤ k ∨ (k = 2 ∧ (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (-conj lam) ^ j) ≠ 0)) (hind : LinearIndependent (↥Qbar) ![1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)]) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := by
    rcases hk with h | ⟨h, -⟩ <;> exact ⟨k - 2, by omega⟩
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hlam0 : lam ≠ 0 := by rintro rfl; simp at hlam1
  have hD : s + lam * u ≠ 0 := by
    intro h
    apply hu
    rw [show u = -s / lam by field_simp; linear_combination h]
    exact div_mem (neg_mem hs) hlam
  have hcm : c (-((m + 2 : ℕ) : ℤ)) ≠ 0 := by rw [hcs]; exact (_root_.map_ne_zero _).2 hck
  have hx : u / s ≠ 0 := div_ne_zero hu0 hs0
  have hr0 : -conj lam ≠ 0 := neg_ne_zero.2 ((_root_.map_ne_zero _).2 hlam0)
  have hv : u / s ∉ Qbar := fun h => hu (by rw [show u = s * (u / s) by field_simp]; exact mul_mem hs h)
  obtain ⟨σ, rfl⟩ : ∃ σ : ↥Qbar, (σ : ℂ) = s := ⟨⟨s, hs⟩, rfl⟩
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ : ↥Qbar, (ℓ : ℂ) = lam := ⟨⟨lam, hlam⟩, rfl⟩
  have hσ : σ ≠ 0 := by rintro rfl; exact hs0 rfl
  have hℓ : ℓ ≠ 0 := by rintro rfl; exact hlam0 rfl
  let γ : ℤ → ↥Qbar := fun j => ⟨c j, hc j⟩
  refine main (P := lpoly (m + 2) γ) (v := u / σ) (w := σ / u) (r := -conj (ℓ : ℂ)) hu hv hσ hℓ
    ?_ ?_ ?_ (lpoly_aeval _ γ hx) ?_ (lpoly_natDegree _ γ fun h => hck (congrArg Subtype.val h))
    ?_ ?_ ?_
  · field_simp
  · field_simp
  · field_simp
    linear_combination -hss
  · rw [show (σ : ℂ) * (1 + ℓ * (u / σ)) = σ + ℓ * u by field_simp]
    exact div_mul_cancel₀ _ hD
  · rwa [lpoly_aeval_zero]
  · linear_combination -hlam1
  · rcases hk with h | ⟨h, h'⟩
    · exact Or.inl (by omega)
    · refine Or.inr ⟨by omega, ?_⟩
      rw [lpoly_aeval _ γ hr0]
      exact mul_ne_zero (pow_ne_zero _ hr0) h'
