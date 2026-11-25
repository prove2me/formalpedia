-- Prove2me | solution 1 for Finset.bernoulliProb_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:05.781597+00:00
-- url     : https://prove2.me/submissions/c81043ee-9076-49cc-9737-b196fd1fceff

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable (U p)
namespace Finset
theorem _root_.solution (P Q : Finset α → Prop) [DecidablePred P] [DecidablePred Q] :
    U.bernoulliProb p P =
      U.bernoulliProb p (fun A => P A ∧ Q A) + U.bernoulliProb p (fun A => P A ∧ ¬Q A) := by
  unfold bernoulliProb
  rw [← sum_filter_add_sum_filter_not (U.powerset.filter P) Q, filter_filter, filter_filter]
end Finset
