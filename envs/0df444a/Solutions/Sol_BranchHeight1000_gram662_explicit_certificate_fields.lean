-- Prove2me | solution 1 for BranchHeight1000.gram662_explicit_certificate_fields
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T23:30:15.093811+00:00
-- url     : https://prove2.me/submissions/b1bc4fe9-2e06-481f-ad24-f8d9d2f03d90

import Theorems.Thm_BranchHeight1000_gram662_left_stirling_margin
import Theorems.Thm_BranchHeight1000_gram662_right_stirling_margin
set_option autoImplicit false
open scoped BigOperators
theorem solution :
  let S : ℕ → ℂ → ℂ := fun M w =>
    (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ)
    + ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ))
  let A : ℕ → ℕ → ℝ → ℝ := fun M N t =>
    (S M (1 / 4 + Complex.I * (t / 2) + N)
      - ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (t / 2) + j)).im
      - t / 2 * Real.log Real.pi
  let E : ℕ → ℕ → ℝ → ℝ := fun M N t =>
    (Nat.factorial (2 * M + 1) : ℝ) * 2 ^ (2 * M + 1) / (2 * M * (2 * Real.pi) ^ (2 * M))
    * ((1 / 4 + N) ^ 2 + (t / 2) ^ 2 : ℝ) ^ (-(M : ℤ))
  (0 ≤ (1017.79497 : ℝ)) ∧ (0 ≤ (1017.79500 : ℝ)) ∧
  (0 < (2 : ℕ)) ∧ (0 < (2 : ℕ)) ∧
  (662 * Real.pi - A 2 0 1017.79497 > E 2 0 1017.79497) ∧
  (A 2 0 1017.79500 - 662 * Real.pi > E 2 0 1017.79500) := by
  dsimp only
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    BranchHeight1000.gram662_left_stirling_margin, BranchHeight1000.gram662_right_stirling_margin⟩
