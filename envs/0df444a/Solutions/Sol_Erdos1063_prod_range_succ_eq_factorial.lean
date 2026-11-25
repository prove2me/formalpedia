-- Prove2me | solution 1 for Erdos1063.prod_range_succ_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:35:53.041115+00:00
-- url     : https://prove2.me/submissions/dcc0f541-e794-4f37-996b-3966902f00a6

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution (m : ℕ) : ∏ y ∈ Finset.range m, (y + 1) = m ! := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; ring
end Erdos1063
