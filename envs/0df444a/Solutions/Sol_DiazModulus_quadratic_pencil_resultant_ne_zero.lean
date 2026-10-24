-- Prove2me | solution 1 for DiazModulus.quadratic_pencil_resultant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:36:51.647881+00:00
-- url     : https://prove2.me/submissions/7ba59854-2634-41cd-8290-c76c119818d4

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_quadratic_pencil_wronskian_identities

open Complex ComplexConjugate

/-! # The resultant of a coprime pencil of quadratics does not vanish

Let `p, q` be coprime with `max(deg p, deg q) = 2`, `[ij] = pᵢqⱼ − pⱼqᵢ` and
`Res = [20]² − [21][10]`. By `quadratic_pencil_wronskian_identities` the Wronskian
`J = p′q − pq′` is `[21]X² + 2[20]X + [10]`, so the coefficient matrix of `(q, p, J)` in
`(1, X, X²)` has determinant `−2·Res`. If `Res = 0`, a non-zero vector `v` kills this matrix from
the left (`Matrix.exists_vecMul_eq_zero_iff`), that is `v₀q + v₁p + v₂J = 0`.
If `v₂ = 0`, then `p` and `q` are proportional, so coprimality makes both constant: impossible.
If `v₂ ≠ 0`, the relation reads `(v₂p′ + v₀)q = p(v₂q′ − v₁)`, so `p ∣ v₂p′ + v₀` and
`q ∣ v₂q′ − v₁` by coprimality. Whichever of `p, q` has degree 2 then divides a polynomial of
degree at most 1, which must vanish; its `X`-coefficient is `2v₂` times the leading coefficient,
non-zero in characteristic zero. ∎
-/

namespace R20_resultant

open DiazModulus Polynomial

/-- A coprime pair with `max deg = 2` admits no non-trivial relation `αq + βp = 0`. -/
theorem no_relation {K : Type*} [Field K] {p q : K[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (α β : K) (hαβ : α ≠ 0 ∨ β ≠ 0)
    (h : C α * q + C β * p = 0) : False := by
  rcases hαβ with hα | hβ
  · have hinv : C α⁻¹ * C α = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hα, C_1]
    have hq : q = C (-(β * α⁻¹)) * p := by
      rw [map_neg, map_mul]; linear_combination C α⁻¹ * h - q * hinv
    have hu : IsUnit p := isCoprime_self.1 (hq ▸ hcop).of_mul_right_right
    have h1 := natDegree_eq_zero_of_isUnit hu
    have h2 : q.natDegree ≤ p.natDegree := hq ▸ natDegree_C_mul_le _ _
    omega
  · have hinv : C β⁻¹ * C β = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hβ, C_1]
    have hp : p = C (-(α * β⁻¹)) * q := by
      rw [map_neg, map_mul]; linear_combination C β⁻¹ * h - p * hinv
    have hu : IsUnit q := isCoprime_self.1 (hp ▸ hcop).of_mul_left_right
    have h1 := natDegree_eq_zero_of_isUnit hu
    have h2 : p.natDegree ≤ q.natDegree := hp ▸ natDegree_C_mul_le _ _
    omega

/-- A quadratic cannot divide `c p′ + d` with `c ≠ 0` (characteristic zero). -/
theorem not_dvd_deriv {K : Type*} [Field K] [CharZero K] {p : K[X]} (hp : p.natDegree = 2)
    (c d : K) (hc : c ≠ 0) (h : p ∣ C c * derivative p + C d) : False := by
  have hlt : (C c * derivative p + C d).natDegree < p.natDegree := by
    have h1 := natDegree_derivative_le p
    have h2 := natDegree_C_mul_le c (derivative p)
    have h3 := natDegree_add_le (C c * derivative p) (C d)
    rw [natDegree_C] at h3
    omega
  have h0 := congrArg (coeff · 1) (eq_zero_of_dvd_of_natDegree_lt h hlt)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hlc : p.coeff 2 ≠ 0 := by
    have := leadingCoeff_ne_zero.2 hp0
    rwa [leadingCoeff, hp] at this
  simp [coeff_derivative] at h0
  norm_num [hc, hlc] at h0

end R20_resultant

open DiazModulus R20_resultant Polynomial in
theorem solution {K : Type*} [Field K] [CharZero K] (p q : K[X])
    (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2) :
    (p.coeff 2 * q.coeff 0 - p.coeff 0 * q.coeff 2) ^ 2
      - (p.coeff 2 * q.coeff 1 - p.coeff 1 * q.coeff 2) * (p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1) ≠ 0 := by
  intro hRes
  have hp : p.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hq : q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  obtain ⟨hJ, -⟩ := DiazModulus.quadratic_pencil_wronskian_identities p q hp hq
  set M : Matrix (Fin 3) (Fin 3) K :=
    !![q.coeff 0, q.coeff 1, q.coeff 2; p.coeff 0, p.coeff 1, p.coeff 2;
      p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1,
      2 * (p.coeff 2 * q.coeff 0 - p.coeff 0 * q.coeff 2),
      p.coeff 2 * q.coeff 1 - p.coeff 1 * q.coeff 2] with hM
  have hdet : M.det = 0 := by
    rw [Matrix.det_fin_three]
    simp only [hM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination (-2) * hRes
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hcol : ∀ j : Fin 3, v 0 * M 0 j + v 1 * M 1 j + v 2 * M 2 j = 0 := by
    intro j
    have := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using this
  have hrel : C (v 0) * q + C (v 1) * p + C (v 2) * (derivative p * q - p * derivative q) = 0 := by
    rw [hJ]
    ext n
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero]
    rcases n with _ | _ | _ | n
    · simpa [hM] using hcol 0
    · simpa [hM] using hcol 1
    · simpa [hM] using hcol 2
    · rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 1 + 1 + 1 by omega),
        coeff_eq_zero_of_natDegree_lt (show q.natDegree < n + 1 + 1 + 1 by omega)]
      simp
  by_cases h2 : v 2 = 0
  · refine no_relation hcop hdeg (v 0) (v 1) ?_ (by simpa [h2] using hrel)
    by_contra hc
    have h0 : v 0 = 0 := by_contra fun h => hc (Or.inl h)
    have h1 : v 1 = 0 := by_contra fun h => hc (Or.inr h)
    exact hv0 (by ext i; fin_cases i <;> simp [h0, h1, h2])
  · have hfac : (C (v 2) * derivative p + C (v 0)) * q = p * (C (v 2) * derivative q - C (v 1)) := by
      linear_combination hrel
    have hdp : p ∣ C (v 2) * derivative p + C (v 0) :=
      hcop.dvd_of_dvd_mul_right (Dvd.intro _ hfac.symm)
    have hdq : q ∣ C (v 2) * derivative q + C (-v 1) :=
      hcop.symm.dvd_of_dvd_mul_right
        (Dvd.intro (C (v 2) * derivative p + C (v 0)) (by rw [map_neg]; linear_combination hfac))
    by_cases hp2 : p.natDegree = 2
    · exact not_dvd_deriv hp2 _ _ h2 hdp
    · exact not_dvd_deriv (by omega) _ _ h2 hdq
