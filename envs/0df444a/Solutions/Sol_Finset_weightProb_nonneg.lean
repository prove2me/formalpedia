-- Prove2me | solution 1 for Finset.weightProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:46.831772+00:00
-- url     : https://prove2.me/submissions/b3fa870e-f6b9-4681-ba47-aeb5866b47a4

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
theorem _root_.solution (hw0 : ∀ a ∈ Ω, 0 ≤ w a) (P : β → Prop) [DecidablePred P] :
    0 ≤ Ω.weightProb w P :=
  sum_nonneg fun a ha => hw0 a (mem_filter.mp ha).1
end Finset
