-- Prove2me | solution 1 for Finset.bernoulliProb_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:00:19.757073+00:00
-- url     : https://prove2.me/submissions/381f4699-3555-44c8-a885-d08c520356c6

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_sum_bernoulliWeight


set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable (U p)
variable {U p}
namespace Finset
theorem _root_.solution : U.bernoulliProb p (fun _ => True) = 1 := by
  rw [bernoulliProb, filter_true_of_mem fun _ _ => trivial, sum_bernoulliWeight]
end Finset
