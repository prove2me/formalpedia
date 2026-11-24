-- Prove2me | solution 1 for BSLambda.LLL.pr_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:18.469776+00:00
-- url     : https://prove2.me/submissions/d08fbf7a-41e9-4c83-87ca-5d7fe1d0e19d

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
namespace BSLambda.LLL
theorem _root_.solution (E : Finset (Cfg β)) : pr E ≤ 1 := by simp [pr]
end BSLambda.LLL
