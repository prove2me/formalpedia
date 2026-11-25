-- Prove2me | solution 1 for DetDLP.quadratic_form_nonneg_iff_hasse_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:29:05.934404+00:00
-- url     : https://prove2.me/submissions/db2ddd2a-5ede-4c3e-9822-0c1dd6f7cd11

import Mathlib

set_option autoImplicit false

/-- Pure algebraic characterization of Hasse's elliptic-curve discriminant bound via the
positive-semidefiniteness of the binary quadratic form `m^2 p - m n (p + 1 - N) + n^2`:
(1) Explicit completing-the-square identity:
    `4 p (m^2 p - m n (p + 1 - N) + n^2) = (2 p m - (p + 1 - N) n)^2 + (4 p - (N - (p + 1))^2) n^2`.
(2) Exact necessary and sufficient condition (`↔`): for any `p > 0` and `N : ℤ`,
    `(∀ m n : ℤ, 0 ≤ m^2 p - m n (p + 1 - N) + n^2) ↔ (N - (p + 1))^2 ≤ 4 p`. -/
theorem solution :
    (∀ (p N m n : ℤ),
      4 * p * (m ^ 2 * p - m * n * (p + 1 - N) + n ^ 2) =
        (2 * p * m - (p + 1 - N) * n) ^ 2 + (4 * p - (N - (p + 1)) ^ 2) * n ^ 2) ∧
    (∀ (p N : ℤ), 0 < p →
      ((∀ m n : ℤ, 0 ≤ m ^ 2 * p - m * n * (p + 1 - N) + n ^ 2) ↔
        (N - (p + 1)) ^ 2 ≤ 4 * p)) := by
  refine ⟨?_, ?_⟩
  · intro p N m n
    ring
  · intro p N hp
    constructor
    · intro hform
      have hspec := hform (p + 1 - N) (2 * p)
      have hid :
          (4 * p - (N - (p + 1)) ^ 2) * p =
            (p + 1 - N) ^ 2 * p - (p + 1 - N) * (2 * p) * (p + 1 - N) + (2 * p) ^ 2 := by
        ring
      have hmul_nonneg : 0 ≤ (4 * p - (N - (p + 1)) ^ 2) * p := by
        linarith
      have hsub_nonneg : 0 ≤ 4 * p - (N - (p + 1)) ^ 2 :=
        nonneg_of_mul_nonneg_left hmul_nonneg hp
      linarith
    · intro hdisc m n
      have hid :
          4 * p * (m ^ 2 * p - m * n * (p + 1 - N) + n ^ 2) =
            (2 * p * m - (p + 1 - N) * n) ^ 2 + (4 * p - (N - (p + 1)) ^ 2) * n ^ 2 := by
        ring
      have hsq1 : 0 ≤ (2 * p * m - (p + 1 - N) * n) ^ 2 := sq_nonneg _
      have hsq2 : 0 ≤ n ^ 2 := sq_nonneg _
      have hdiff : 0 ≤ 4 * p - (N - (p + 1)) ^ 2 := by linarith
      have hterm2 : 0 ≤ (4 * p - (N - (p + 1)) ^ 2) * n ^ 2 := mul_nonneg hdiff hsq2
      have hprod : 0 ≤ (m ^ 2 * p - m * n * (p + 1 - N) + n ^ 2) * (4 * p) := by
        linarith
      have h4p : 0 < 4 * p := by linarith
      exact nonneg_of_mul_nonneg_left hprod h4p
