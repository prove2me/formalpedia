-- Prove2me | solution 1 for DiazModulus.quadratic_pencil_wronskian_span
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:34:25.755979+00:00
-- url     : https://prove2.me/submissions/c10bbb36-d7fa-4b97-b3f7-4b0b81538bfb

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_quadratic_pencil_wronskian_identities
import Theorems.Thm_DiazModulus_quadratic_pencil_resultant_ne_zero

open Complex ComplexConjugate

/-! # `q`, `p` and the Wronskian span the polynomials of degree at most 2

Let `p, q` be coprime with `max(deg p, deg q) = 2` over a field of characteristic zero. By
`quadratic_pencil_wronskian_identities`, `J = p′q − pq′ = [21]X² + 2[20]X + [10]`, so the
coefficient matrix `M` of `(q, p, J)` in the basis `(1, X, X²)` has determinant `−2·Res`, where
`Res = [20]² − [21][10]`. By `quadratic_pencil_resultant_ne_zero`, `Res ≠ 0`, so `M` is
invertible. For `R` of degree at most 2 with coefficient vector `r`, the vector `v = r M⁻¹`
satisfies `v M = r` (`Matrix.nonsing_inv_mul`), which says coefficient by coefficient that
`R = v₀q + v₁p + v₂J`; the coefficients of degree at least 3 vanish on both sides. ∎
-/

open DiazModulus Polynomial in
theorem solution {K : Type*} [Field K] [CharZero K] (p q : K[X])
    (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2) (R : K[X]) (hR : R.natDegree ≤ 2) :
    ∃ a b c : K, R = C a * q + C b * p + C c * (derivative p * q - p * derivative q) := by
  have hp : p.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hq : q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  obtain ⟨hJ, -⟩ := DiazModulus.quadratic_pencil_wronskian_identities p q hp hq
  have hRes := DiazModulus.quadratic_pencil_resultant_ne_zero p q hcop hdeg
  set M : Matrix (Fin 3) (Fin 3) K :=
    !![q.coeff 0, q.coeff 1, q.coeff 2; p.coeff 0, p.coeff 1, p.coeff 2;
      p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1,
      2 * (p.coeff 2 * q.coeff 0 - p.coeff 0 * q.coeff 2),
      p.coeff 2 * q.coeff 1 - p.coeff 1 * q.coeff 2] with hM
  have hdet : M.det = -2 * ((p.coeff 2 * q.coeff 0 - p.coeff 0 * q.coeff 2) ^ 2
      - (p.coeff 2 * q.coeff 1 - p.coeff 1 * q.coeff 2) * (p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1)) := by
    rw [Matrix.det_fin_three]
    simp only [hM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    ring
  have hunit : IsUnit M.det := by
    rw [hdet]; exact isUnit_iff_ne_zero.2 (mul_ne_zero (by norm_num) hRes)
  set r : Fin 3 → K := ![R.coeff 0, R.coeff 1, R.coeff 2] with hr
  set v : Fin 3 → K := Matrix.vecMul r M⁻¹ with hvdef
  have hv : Matrix.vecMul v M = r := by
    rw [hvdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]
  have hcol : ∀ j : Fin 3, v 0 * M 0 j + v 1 * M 1 j + v 2 * M 2 j = r j := by
    intro j
    have := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using this
  refine ⟨v 0, v 1, v 2, ?_⟩
  rw [hJ]
  ext n
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  rcases n with _ | _ | _ | n
  · simpa [hM, hr] using (hcol 0).symm
  · simpa [hM, hr] using (hcol 1).symm
  · simpa [hM, hr] using (hcol 2).symm
  · rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 1 + 1 + 1 by omega),
      coeff_eq_zero_of_natDegree_lt (show q.natDegree < n + 1 + 1 + 1 by omega),
      coeff_eq_zero_of_natDegree_lt (show R.natDegree < n + 1 + 1 + 1 by omega)]
    simp
