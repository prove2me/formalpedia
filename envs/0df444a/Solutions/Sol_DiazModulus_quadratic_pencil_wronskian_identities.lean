-- Prove2me | solution 1 for DiazModulus.quadratic_pencil_wronskian_identities
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:38:30.656099+00:00
-- url     : https://prove2.me/submissions/8e57b80b-9783-42af-9298-b5746a2fbb1d

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The Wronskian of a pencil of quadratics

For `p, q` of degree at most 2, write `p = p₂X² + p₁X + p₀`, `q = q₂X² + q₁X + q₀` (a polynomial of
`natDegree ≤ 2` is determined by its coefficients in degrees 0, 1, 2). The Wronskian
`J = p′q − pq′` is then `[21]X² + 2[20]X + [10]` with `[ij] = pᵢqⱼ − pⱼqᵢ`, and
`J² = d₂p² + d₁pq + d₀q²`, where `d₂X² + d₁X + d₀` is the discriminant in `Y` of `p(Y) − Xq(Y)`.
Both are polynomial identities in the six coefficients: after substituting the two quadratic
expansions, the derivative is computed by `simp` and the identities close by `ring`.
This works over any commutative ring.
-/

namespace R20_wronskian

open DiazModulus Polynomial

/-- A polynomial of degree at most 2 is its quadratic expansion. -/
theorem quad_expand {K : Type*} [CommRing K] (p : K[X]) (hp : p.natDegree ≤ 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- The two identities for explicit quadratics. -/
theorem identities_explicit {K : Type*} [CommRing K] (a b c d e f : K) :
    let P : K[X] := C a * X ^ 2 + C b * X + C c
    let Q : K[X] := C d * X ^ 2 + C e * X + C f
    derivative P * Q - P * derivative Q =
        C (a * e - b * d) * X ^ 2 + C (2 * (a * f - c * d)) * X + C (b * f - c * e) ∧
    (derivative P * Q - P * derivative Q) ^ 2 =
        C (e ^ 2 - 4 * d * f) * P ^ 2 + C (4 * (a * f + c * d) - 2 * b * e) * (P * Q)
        + C (b ^ 2 - 4 * a * c) * Q ^ 2 := by
  intro P Q
  have hJ : derivative P * Q - P * derivative Q =
      C (a * e - b * d) * X ^ 2 + C (2 * (a * f - c * d)) * X + C (b * f - c * e) := by
    simp only [P, Q, derivative_add, derivative_mul, derivative_C, derivative_X_sq,
      derivative_X, map_sub, map_mul, C_ofNat]
    ring
  refine ⟨hJ, ?_⟩
  rw [hJ]
  simp only [P, Q, map_sub, map_mul, map_add, map_ofNat, map_pow]
  ring

end R20_wronskian

open DiazModulus R20_wronskian Polynomial in
theorem solution {K : Type*} [CommRing K] (p q : K[X])
    (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    derivative p * q - p * derivative q =
        C (p.coeff 2 * q.coeff 1 - p.coeff 1 * q.coeff 2) * X ^ 2
        + C (2 * (p.coeff 2 * q.coeff 0 - p.coeff 0 * q.coeff 2)) * X
        + C (p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1) ∧
    (derivative p * q - p * derivative q) ^ 2 =
        C (q.coeff 1 ^ 2 - 4 * q.coeff 2 * q.coeff 0) * p ^ 2
        + C (4 * (p.coeff 2 * q.coeff 0 + p.coeff 0 * q.coeff 2) - 2 * p.coeff 1 * q.coeff 1) * (p * q)
        + C (p.coeff 1 ^ 2 - 4 * p.coeff 2 * p.coeff 0) * q ^ 2 := by
  have h := identities_explicit (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 2) (q.coeff 1)
    (q.coeff 0)
  simp only [← quad_expand p hp, ← quad_expand q hq] at h
  exact h
