-- Prove2me | solution 1 for Finset.weightProb_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:51.545099+00:00
-- url     : https://prove2.me/submissions/accf79d3-1215-4059-9216-1c80fefc4200

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
theorem _root_.solution (hw0 : ∀ a ∈ Ω, 0 ≤ w a) {P Q : β → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ a, P a → Q a) : Ω.weightProb w P ≤ Ω.weightProb w Q :=
  sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun a _ => h a) fun a ha _ =>
    hw0 a (mem_filter.mp ha).1
end Finset
