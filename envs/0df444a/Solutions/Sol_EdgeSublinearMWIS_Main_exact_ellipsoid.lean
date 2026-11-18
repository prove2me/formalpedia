-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.exact_ellipsoid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:10:56.524853+00:00
-- url     : https://prove2.me/submissions/81cfeb4d-3ca7-4c7b-bb97-fc36b61ca5ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EdgeSublinearMWIS_Main_binary_hull_polynomial_description
import Theorems.Thm_EdgeSublinearMWIS_Main_exact_binary_oracle_feasibility

theorem solution : ∃ (E : EdgeSublinearMWIS.Main.Program)
    (bound queries work coordinates : Polynomial ℕ),
    EdgeSublinearMWIS.Main.ExactEllipsoid E bound queries work coordinates := by
  obtain ⟨E,queries,work,coordinates,h⟩ := EdgeSublinearMWIS.Main.exact_binary_oracle_feasibility
    (Polynomial.C 10*Polynomial.X^3) EdgeSublinearMWIS.Main.binary_hull_polynomial_description
  exact ⟨E,Polynomial.C 10*Polynomial.X^3,queries,work,coordinates,h⟩
