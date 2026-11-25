-- Prove2me | solution 1 for Erdos679.sum_log_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:20:32.055132+00:00
-- url     : https://prove2.me/submissions/aa46f931-70a0-46e6-9a39-ee0fb28e8073

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

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (m : ℕ) :
    ∑ i ∈ Finset.range m, log ((i + 1 : ℕ) : ℝ) = log (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring
end Erdos679
