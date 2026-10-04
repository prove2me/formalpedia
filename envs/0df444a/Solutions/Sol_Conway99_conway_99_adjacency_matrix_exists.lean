-- Prove2me | solution 1 for Conway99.conway_99_adjacency_matrix_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:59:00.806066+00:00
-- url     : https://prove2.me/submissions/3873e3f2-9944-4a09-84ae-6455c21793d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Conway99_triangle_system_iff_adjacency_matrix
import Theorems.Thm_Conway99_conway_99_triangle_system_exists

open scoped BigOperators

theorem solution :
    ∃ A : Matrix (Fin 99) (Fin 99) ℕ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i j, A i j = A j i) ∧
      (∀ i, A i i = 0) ∧
      (∀ i j, (∑ k, A i k * A k j) + A i j = (if i = j then 12 else 0) + 2) := by
  exact Conway99.triangle_system_iff_adjacency_matrix.mp
    Conway99.conway_99_triangle_system_exists

#print axioms solution
