-- Prove2me | solution 1 for EqualTwoSquares.explicit_family_solution
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:19.843979+00:00
-- url     : https://prove2.me/submissions/a43b2513-f973-4be7-a4c9-c14eba4df13b

-- Public-mission submission for EqualTwoSquares.explicit_family_solution.

import Mathlib

theorem solution {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 ∧
      (0 < (1 : ℤ) ∧ 0 < n^2 - n + 1 ∧ 0 < 2 * n - 1 ∧ 0 < n^2 - n - 1) ∧
        ((1 : ℤ) ≠ 2 * n - 1 ∧
          (1 : ℤ) ≠ n^2 - n - 1 ∧
            (1 : ℤ) ≠ n^2 - n + 1 ∧
              2 * n - 1 ≠ n^2 - n - 1 ∧
                2 * n - 1 ≠ n^2 - n + 1 ∧
                  n^2 - n - 1 ≠ n^2 - n + 1) := by
  have h1 : (1 : ℤ) < 2 * n - 1 := by nlinarith
  have h2 : 2 * n - 1 < n^2 - n - 1 := by nlinarith
  have h3 : n^2 - n - 1 < n^2 - n + 1 := by nlinarith
  have h12 : (1 : ℤ) < n^2 - n - 1 := lt_trans h1 h2
  have h13 : (1 : ℤ) < n^2 - n + 1 := lt_trans h12 h3
  have h23 : 2 * n - 1 < n^2 - n + 1 := lt_trans h2 h3
  constructor
  · ring
  constructor
  · exact ⟨by norm_num, by linarith, by linarith, by linarith⟩
  · exact ⟨ne_of_lt h1, ne_of_lt h12, ne_of_lt h13,
      ne_of_lt h2, ne_of_lt h23, ne_of_lt h3⟩
