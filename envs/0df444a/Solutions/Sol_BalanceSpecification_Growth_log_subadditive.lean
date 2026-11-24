-- Prove2me | solution 1 for BalanceSpecification.Growth.log_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:35.229806+00:00
-- url     : https://prove2.me/submissions/77356164-3ead-41e0-8f2a-f6e20fdfee8c

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) : Subadditive (fun n => Real.log (a n)) := by
  intro m n
  have hp i : 0 < a i := lt_of_lt_of_le zero_lt_one (ha i)
  calc
    Real.log (a (m + n)) ≤ Real.log (a m * a n) :=
      Real.log_le_log (hp _) (hs m n)
    _ = Real.log (a m) + Real.log (a n) := Real.log_mul (hp _).ne' (hp _).ne'
end BalanceSpecification.Growth
