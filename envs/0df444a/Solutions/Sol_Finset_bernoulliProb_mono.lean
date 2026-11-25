-- Prove2me | solution 1 for Finset.bernoulliProb_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:07.9565+00:00
-- url     : https://prove2.me/submissions/c082c89a-10d5-4362-bca2-057305dbfbf3

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_bernoulliWeight_nonneg


set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable (U p)
variable {U p}
namespace Finset
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) {P Q : Finset α → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ A, P A → Q A) : U.bernoulliProb p P ≤ U.bernoulliProb p Q :=
  sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun A _ => h A) fun A _ _ =>
    bernoulliWeight_nonneg h0 h1 A
end Finset
