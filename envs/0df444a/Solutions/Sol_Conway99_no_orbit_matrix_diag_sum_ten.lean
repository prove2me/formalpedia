-- Prove2me | solution 1 for Conway99.no_orbit_matrix_diag_sum_ten
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T13:36:25.402724+00:00
-- url     : https://prove2.me/submissions/db760b8f-da87-416e-b36b-1e220e671a1e

import Mathlib
import Theorems.Thm_Conway99_no_orbit_matrix_ten_of_exists_four
import Theorems.Thm_Conway99_no_orbit_matrix_ten_of_no_four

theorem solution
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : (∑ i, C i i) = 10) : False := by
  by_cases h : ∃ i, C i i = 4
  · exact Conway99.no_orbit_matrix_ten_of_exists_four C hsymm hrow hsq hdiag htr h
  · push_neg at h
    exact Conway99.no_orbit_matrix_ten_of_no_four C hsymm hrow hsq hdiag htr h
