-- Prove2me | solution 1 for BranchHeight1000.gram655_explicit_certificate_fields
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T16:03:48.332863+00:00
-- url     : https://prove2.me/submissions/49ea5621-8073-44f1-ba74-49d2171a45a4

import Theorems.Thm_BranchHeight1000_gram655_left_stirling_margin
import Theorems.Thm_BranchHeight1000_gram655_right_stirling_margin
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
  (0 ≤ (1009.14258 : ℝ)) ∧ (0 ≤ (1009.14261 : ℝ)) ∧
  (0 < (2 : ℕ)) ∧ (0 < (2 : ℕ)) ∧
  (655 * Real.pi - A 2 0 1009.14258 > E 2 0 1009.14258) ∧
  (A 2 0 1009.14261 - 655 * Real.pi > E 2 0 1009.14261) := by
  dsimp only
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    BranchHeight1000.gram655_left_stirling_margin, BranchHeight1000.gram655_right_stirling_margin⟩
