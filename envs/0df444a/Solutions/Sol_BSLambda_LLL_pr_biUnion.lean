-- Prove2me | solution 1 for BSLambda.LLL.pr_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:53:11.075892+00:00
-- url     : https://prove2.me/submissions/d21c5295-8ca8-49d4-9020-6fc1206c29c8

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_eq_div
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution {κ : Type*} {T : Finset κ} {E : κ → Finset (Cfg β)}
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (E i) (E j)) :
    pr (T.biUnion E) = ∑ i ∈ T, pr (E i) := by
  simp only [pr_eq_div]
  rw [Finset.card_biUnion hdisj, Nat.cast_sum, Finset.sum_div]
end BSLambda.LLL
