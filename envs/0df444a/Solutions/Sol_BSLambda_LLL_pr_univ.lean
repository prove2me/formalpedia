-- Prove2me | solution 1 for BSLambda.LLL.pr_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:46:41.323056+00:00
-- url     : https://prove2.me/submissions/9c77e98e-7ecf-45f7-94e3-292ee7b9f8a3

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_empty
attribute [local simp] BSLambda.LLL.pr_empty

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
omit [(a : A) → DecidableEq (β a)]
variable [∀ a, Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution : pr (Finset.univ : Finset (Cfg β)) = 1 := by simp [pr]
end BSLambda.LLL
