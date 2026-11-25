-- Prove2me | solution 1 for Finset.avoids_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:55.865538+00:00
-- url     : https://prove2.me/submissions/218133a8-be52-4a86-8e54-524f6f2b9330

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_bernoulliProb_true
attribute [local simp] Finset.bernoulliProb_true

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
omit [∀ i, DecidablePred (E i)]
namespace Finset
theorem _root_.solution [DecidableEq ι] {i : ι} {S : Finset ι} {a : β} :
    Avoids E (insert i S) a ↔ ¬E i a ∧ Avoids E S a := by
  simp [Avoids]
end Finset
