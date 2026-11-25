-- Prove2me | solution 1 for Finset.weightProb_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:53.075874+00:00
-- url     : https://prove2.me/submissions/5bf8d0c3-ca70-4996-ad1b-c527e492b939

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
variable {β : Type*}
variable {Ω : Finset β} {w : β → ℝ}
namespace Finset
theorem _root_.solution (Ω : Finset β) (w : β → ℝ) (P Q : β → Prop) [DecidablePred P]
    [DecidablePred Q] :
    Ω.weightProb w P =
      Ω.weightProb w (fun a => P a ∧ Q a) + Ω.weightProb w (fun a => P a ∧ ¬Q a) := by
  unfold weightProb
  rw [← sum_filter_add_sum_filter_not (Ω.filter P) Q, filter_filter, filter_filter]
end Finset
