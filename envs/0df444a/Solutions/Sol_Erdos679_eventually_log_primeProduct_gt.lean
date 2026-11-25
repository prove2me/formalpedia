-- Prove2me | solution 1 for Erdos679.eventually_log_primeProduct_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:53.439688+00:00
-- url     : https://prove2.me/submissions/44d4fe60-16b9-4b5f-a17f-1e46da41538c

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_Analytic
public import Theorems.Thm_Erdos679_factorial_le_primeProduct

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution :
    ∀ᶠ m : ℕ in atTop, m * (log m - 2) < log (primeProduct m : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hl := Stirling.le_log_factorial_stirling (show m ≠ 0 by omega)
  have hlog : 0 ≤ log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hconstant : 0 ≤ log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.two_le_pi])
  have hprod : log (m.factorial : ℝ) ≤ log (primeProduct m : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast factorial_le_primeProduct m)
  nlinarith
end Erdos679
