-- Prove2me | solution 1 for Erdos685.trivial_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:46:02.607485+00:00
-- url     : https://prove2.me/submissions/77f67b13-d98d-4d02-9654-ab5a5dc682db

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_Erdos685ElementaryLowerBound_Solution
public import Theorems.Thm_Erdos685_choose_le_pow_omega

set_option autoImplicit false
@[expose] public section
public section
open Real Finset
open scoped ArithmeticFunction.omega
open Erdos685
namespace Erdos685
theorem _root_.solution (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    log (n.choose k : ℝ) / log (n : ℝ) ≤ (ω (n.choose k) : ℝ) := by
  have hn : 1 < n := by omega
  have hp : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  apply (div_le_iff₀ hp).mpr
  have hpow : (n.choose k : ℝ) ≤ (n : ℝ) ^ (ω (n.choose k)) := by
    exact_mod_cast choose_le_pow_omega (by omega) hkn.le
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.choose_pos hkn.le)) hpow
  simpa only [Real.log_pow] using hlog
end Erdos685
