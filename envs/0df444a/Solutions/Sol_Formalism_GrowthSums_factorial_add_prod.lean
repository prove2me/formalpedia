-- Prove2me | solution 1 for Formalism.GrowthSums.factorial_add_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:05.280966+00:00
-- url     : https://prove2.me/submissions/16f2cfbd-a669-4dc3-83aa-39c2c63b7ab0

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Coarse

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
theorem _root_.solution (m k : ℕ) :
    (((m + k).factorial : ℕ) : ℚ) =
      (m.factorial : ℚ) * (k.factorial : ℚ) * ∏ y ∈ Ico 1 (k + 1), (1 + (m : ℚ) / y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : m + (k + 1) = (m + k) + 1 := by omega
    rw [h1, Nat.factorial_succ (m + k), Nat.factorial_succ k,
      Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    rw [ih]
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring
end Formalism.GrowthSums
