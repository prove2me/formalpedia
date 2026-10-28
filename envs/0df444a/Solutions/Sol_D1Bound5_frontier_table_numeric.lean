-- Prove2me | solution 1 for D1Bound5.frontier_table_numeric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:23.764863+00:00
-- url     : https://prove2.me/submissions/17b94720-33a0-468c-8a4a-25dc02209ffc

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FrontierScalarReduction_Definitions
import Definitions.Def_D1Bound5_FrontierTableNumeric_Definitions
import Theorems.Thm_D1Bound5_frontier_quadratic_interval_exclusion

section
namespace D1Bound5





/-- All five frontier constants pass the exact rational endpoint check.
This is only the scalar closing step; the determinant inequality is
explicitly displayed here and supplied by the tuple assembly. -/
theorem _root_.solution (alpha beta target tau : ℝ)
    (hrow : FrontierTableRow alpha beta target) (htau : (2/3 : ℝ) < tau)
    (hscalar : tau ≤ 2*frontierK alpha beta*tau^2+
      frontierL alpha beta*frontierP alpha beta*tau+frontierJ alpha beta) :
    target < tau := by
  rcases hrow with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · by_contra hbad
    apply frontier_quadratic_interval_exclusion
      (2*frontierK (1) (8))
      (frontierL (1) (8)*frontierP (1) (8)-1)
      (frontierJ (1) (8)) (2/3) (27/8) tau
      (by norm_num [frontierK]) htau (le_of_not_gt hbad)
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · nlinarith only [hscalar]
  · by_contra hbad
    apply frontier_quadratic_interval_exclusion
      (2*frontierK (140/99) (4))
      (frontierL (140/99) (4)*frontierP (140/99) (4)-1)
      (frontierJ (140/99) (4)) (2/3) (3) tau
      (by norm_num [frontierK]) htau (le_of_not_gt hbad)
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · nlinarith only [hscalar]
  · by_contra hbad
    apply frontier_quadratic_interval_exclusion
      (2*frontierK (12/7) (3))
      (frontierL (12/7) (3)*frontierP (12/7) (3)-1)
      (frontierJ (12/7) (3)) (2/3) (11/4) tau
      (by norm_num [frontierK]) htau (le_of_not_gt hbad)
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · nlinarith only [hscalar]
  · by_contra hbad
    apply frontier_quadratic_interval_exclusion
      (2*frontierK (2) (3))
      (frontierL (2) (3)*frontierP (2) (3)-1)
      (frontierJ (2) (3)) (2/3) (29/10) tau
      (by norm_num [frontierK]) htau (le_of_not_gt hbad)
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · nlinarith only [hscalar]
  · by_contra hbad
    apply frontier_quadratic_interval_exclusion
      (2*frontierK (20/9) (3))
      (frontierL (20/9) (3)*frontierP (20/9) (3)-1)
      (frontierJ (20/9) (3)) (2/3) (3) tau
      (by norm_num [frontierK]) htau (le_of_not_gt hbad)
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · norm_num [frontierK, frontierL, frontierP, frontierJ, frontierQ]
    · nlinarith only [hscalar]

end D1Bound5
end
