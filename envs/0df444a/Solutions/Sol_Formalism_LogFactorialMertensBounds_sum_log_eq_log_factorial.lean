-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.sum_log_eq_log_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:27.023455+00:00
-- url     : https://prove2.me/submissions/d2eb5b4c-2482-4129-a9ae-149f4e88ebbc

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution (k : ℕ) :
    ∑ n ∈ Finset.Ioc 0 k, Real.log n = Real.log (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))]
    ring
end Formalism.LogFactorialMertensBounds
