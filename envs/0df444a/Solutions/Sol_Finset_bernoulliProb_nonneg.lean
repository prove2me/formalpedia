-- Prove2me | solution 1 for Finset.bernoulliProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:17.298026+00:00
-- url     : https://prove2.me/submissions/e8427658-e708-4ca9-8bd6-52dc4b7c95fc

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Theorems.Thm_Finset_bernoulliWeight_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
namespace Finset
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) (P : Finset α → Prop) [DecidablePred P] :
    0 ≤ U.bernoulliProb p P :=
  sum_nonneg fun A _ => bernoulliWeight_nonneg h0 h1 A
end Finset
