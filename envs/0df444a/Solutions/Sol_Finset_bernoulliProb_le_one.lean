-- Prove2me | solution 1 for Finset.bernoulliProb_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:38.803102+00:00
-- url     : https://prove2.me/submissions/f0f98aa5-4ec2-4e03-a363-5db86711d192

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Theorems.Thm_Finset_bernoulliWeight_nonneg
public import Theorems.Thm_Finset_sum_bernoulliWeight

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
namespace Finset
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) (P : Finset α → Prop) [DecidablePred P] :
    U.bernoulliProb p P ≤ 1 := by
  rw [← sum_bernoulliWeight U p]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun A _ _ =>
    bernoulliWeight_nonneg h0 h1 A
end Finset
