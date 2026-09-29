-- Prove2me | solution 1 for EisensteinWeightOne.chiNegThree_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a35bbd78-bc1f-52bc-9177-c7676dad1527

import Mathlib.Tactic
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinWeightOne_chiNegThree_mul

open EisensteinWeightOne

theorem solution (m n : ℕ) :
    chiNegThree (m * n) = chiNegThree m * chiNegThree n := by
  simp only [chiNegThree]
  rw [Nat.mul_mod]
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with h | h | h <;> rcases hn with h' | h' | h' <;> rw [h, h'] <;> decide

end S_EisensteinWeightOne_chiNegThree_mul
end P2MW
export P2MW.S_EisensteinWeightOne_chiNegThree_mul (solution)
