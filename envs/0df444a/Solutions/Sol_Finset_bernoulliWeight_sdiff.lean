-- Prove2me | solution 1 for Finset.bernoulliWeight_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:22.806335+00:00
-- url     : https://prove2.me/submissions/ca272445-1e64-49c3-8b3d-000d478998ec

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
theorem _root_.solution {A : Finset α} (hA : A ⊆ U) :
    U.bernoulliWeight (1 - p) (U \ A) = U.bernoulliWeight p A := by
  rw [bernoulliWeight, bernoulliWeight, sdiff_sdiff_eq_self hA, sub_sub_cancel, mul_comm]
end Finset
