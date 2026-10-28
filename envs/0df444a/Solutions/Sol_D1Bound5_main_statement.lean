-- Prove2me | solution 1 for D1Bound5.main_statement
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T21:30:27.643992+00:00
-- url     : https://prove2.me/submissions/2f1ca8e1-920a-48fd-94d4-6d050e6faea3

import Theorems.Thm_D1Bound5_mainStatement_iff_three_ordered_cases
import Theorems.Thm_D1Bound5_IsD1Tuple_all_large_impossible
import Theorems.Thm_D1Bound5_IsD1Tuple_not_one_small
import Theorems.Thm_D1Bound5_IsD1Tuple_not_three_small
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_nondegenerate_impossible
import Theorems.Thm_D1Bound5_IsD1Tuple_degenerate_first_pair_impossible

open scoped NumberField
open Module

universe u

namespace D1Bound5

/-- The full-ring cardinality bound, assembled from the three exhaustive
ordered cases. The entries may have equal moduli, and pair square roots
may be zero. This research module is not accepted until its entire import
closure has compiled and passed the project verification gates. -/
theorem _root_.solution : MainStatement.{u} := by
  apply mainStatement_iff_three_ordered_cases.mpr
  intro K _ _ _ hK phi
  refine ⟨?_, ?_, ?_⟩
  · intro t ht hmon hlarge
    exact ht.all_large_impossible hK phi t hmon hlarge
  · intro t ht hmon hfirst hsecond
    exact ht.not_one_small hK phi t hmon hfirst hsecond
  · intro t ht hmon hsecond
    by_cases hthird : ‖phi (t 2 : K)‖ < 3
    · exact ht.not_three_small hK phi t hmon hthird
    · by_cases hprod : t 0*t 1+1 = 0
      · exact ht.degenerate_first_pair_impossible hK phi t hmon hprod
      · exact ht.two_small_nondegenerate_impossible hK phi t hmon hsecond
          (le_of_not_gt hthird) hprod

end D1Bound5

