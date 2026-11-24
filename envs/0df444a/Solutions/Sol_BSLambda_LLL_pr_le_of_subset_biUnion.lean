-- Prove2me | solution 1 for BSLambda.LLL.pr_le_of_subset_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:53:45.315801+00:00
-- url     : https://prove2.me/submissions/f02df5c5-0fce-42fa-87a0-3fbf267fe546

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_mono
public import Theorems.Thm_BSLambda_LLL_pr_biUnion_le

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
variable [∀ a, Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution {κ : Type*} {E : Finset (Cfg β)}
    (T : Finset κ) (f : κ → Finset (Cfg β)) (h : E ⊆ T.biUnion f) :
    pr E ≤ ∑ i ∈ T, pr (f i) := (pr_mono h).trans (pr_biUnion_le T f)
end BSLambda.LLL
