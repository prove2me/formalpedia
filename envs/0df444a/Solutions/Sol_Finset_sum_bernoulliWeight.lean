-- Prove2me | solution 1 for Finset.sum_bernoulliWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:23.451532+00:00
-- url     : https://prove2.me/submissions/dffa2ffd-93d2-4eee-be3a-83e47f59b857

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
variable (U p)
namespace Finset
theorem _root_.solution : ∑ A ∈ U.powerset, U.bernoulliWeight p A = 1 := by
  have := sum_pow_mul_eq_add_pow p (1 - p) U
  rw [add_sub_cancel, one_pow] at this
  rw [← this]
  exact sum_congr rfl fun A hA => by
    rw [bernoulliWeight, card_sdiff_of_subset (mem_powerset.mp hA)]
end Finset
