-- Prove2me | solution 1 for BSLambda.LLL.pr_inter_add_pr_compl_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:29.791786+00:00
-- url     : https://prove2.me/submissions/323c3c7c-8df7-45d2-a8e2-8e6dd409df51

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution (E F : Finset (Cfg β)) :
    pr (E ∩ F) + pr (Eᶜ ∩ F) = pr F := by
  rw [Finset.inter_comm E F, Finset.inter_comm Eᶜ F, ← Finset.sdiff_eq_inter_compl, pr, pr, pr,
    ← NNRat.cast_add, Finset.dens_inter_add_dens_sdiff]
end BSLambda.LLL
