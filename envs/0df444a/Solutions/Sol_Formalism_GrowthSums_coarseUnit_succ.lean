-- Prove2me | solution 1 for Formalism.GrowthSums.coarseUnit_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:17.182832+00:00
-- url     : https://prove2.me/submissions/18409dad-0806-4352-8c9c-a70ad7b14b4a

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Coarse
import Theorems.Thm_Formalism_GrowthSums_factorial_add_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
namespace Formalism.GrowthSums
theorem _root_.solution (P n : ℕ) (hP : 1 ≤ P) :
    coarseUnit P (n + 1) = coarseUnit P n * ∏ y ∈ Ico 1 P, (1 + (P : ℚ) * n / y) := by
  have hPq : (P : ℚ) ≠ 0 := by exact_mod_cast (show P ≠ 0 by omega)
  have key := factorial_add_prod (P * n) P
  push_cast at key
  rw [Finset.prod_Ico_succ_top hP, mul_div_cancel_left₀ _ hPq] at key
  have hfP : (P.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero P
  have hfn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  unfold coarseUnit
  rw [show P * (n + 1) = P * n + P by ring, key, Nat.factorial_succ n]
  push_cast
  field_simp
  ring
end Formalism.GrowthSums
