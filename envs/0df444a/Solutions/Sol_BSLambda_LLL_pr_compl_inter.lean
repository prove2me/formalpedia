-- Prove2me | solution 1 for BSLambda.LLL.pr_compl_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:56.884602+00:00
-- url     : https://prove2.me/submissions/457e133c-ef9a-4390-b470-3f8410009ca4

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_inter_add_pr_compl_inter

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution (E F : Finset (Cfg β)) : pr (Eᶜ ∩ F) = pr F - pr (E ∩ F) :=
  eq_sub_of_add_eq' (pr_inter_add_pr_compl_inter E F)
end BSLambda.LLL
