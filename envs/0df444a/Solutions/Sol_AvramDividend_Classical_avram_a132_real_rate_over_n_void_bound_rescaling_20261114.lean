-- Prove2me | solution 1 for AvramDividend.Classical.avram_a132_real_rate_over_n_void_bound_rescaling_20261114
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:20:11.518311+00:00
-- url     : https://prove2.me/submissions/5cb56145-6f5c-4b00-92bd-c94d6d38a473

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem solution
    (r q : ℝ) (n : ℕ) (hn : 0 < n)
    (hLo : r / (n : ℝ) - (r / (n : ℝ)) ^ 2 ≤ q)
    (hHi : q ≤ r / (n : ℝ)) :
    r - r ^ 2 / (n : ℝ) ≤ (n : ℝ) * q ∧
      (n : ℝ) * q ≤ r := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have h := mul_le_mul_of_nonneg_left hLo hn'.le
    have e : (n : ℝ) * (r / n - (r / n) ^ 2) = r - r ^ 2 / n := by
      field_simp
    linarith
  · have h := mul_le_mul_of_nonneg_left hHi hn'.le
    have e : (n : ℝ) * (r / n) = r := by field_simp
    linarith
