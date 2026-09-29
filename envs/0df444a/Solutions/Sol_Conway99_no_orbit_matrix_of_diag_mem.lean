-- Prove2me | solution 1 for Conway99.no_orbit_matrix_of_diag_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T13:20:15.698461+00:00
-- url     : https://prove2.me/submissions/7f145b8d-9afa-43b5-bb7a-83c4f6366a9e

import Mathlib
import Theorems.Thm_Conway99_orbit_matrix_diag_sum_mem
import Theorems.Thm_Conway99_no_orbit_matrix_diag_sum_twentyfour
import Theorems.Thm_Conway99_no_orbit_matrix_diag_sum_ten

theorem solution :
    ¬ ∃ C : Matrix (Fin 9) (Fin 9) ℕ, (∀ i j, C i j = C j i) ∧ (∀ i, ∑ j, C i j = 14) ∧
      (∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22) ∧
      (∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4) := by
  rintro ⟨C, hs, hr, hq, hd⟩
  rcases Conway99.orbit_matrix_diag_sum_mem C hs hr hq hd with h | h
  · exact Conway99.no_orbit_matrix_diag_sum_ten C hs hr hq hd h
  · exact Conway99.no_orbit_matrix_diag_sum_twentyfour C hs hr hq hd h
