-- Prove2me | solution 1 for Finset.bernoulliWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:25.614735+00:00
-- url     : https://prove2.me/submissions/8032bdaf-e2c6-43d5-bee2-7ea30c6b577b

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
namespace Finset
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) (A : Finset α) :
    0 ≤ U.bernoulliWeight p A := by
  unfold bernoulliWeight
  have : 0 ≤ 1 - p := by linarith
  positivity
end Finset
