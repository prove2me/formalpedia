-- Prove2me | solution 1 for Finset.bernoulliProb_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:40.323531+00:00
-- url     : https://prove2.me/submissions/fa1fd309-60f6-4fe0-9d7f-e8136bd61e1a

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
theorem _root_.solution {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ A ⊆ U, P A ↔ Q A) : U.bernoulliProb p P = U.bernoulliProb p Q :=
  sum_congr (filter_congr fun A hA => h A (mem_powerset.mp hA)) fun _ _ => rfl
end Finset
