-- Prove2me | solution 1 for BSLambda.LLL.pr_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:18.990667+00:00
-- url     : https://prove2.me/submissions/c0f9cd24-48e7-42a5-88c2-f82becff60b1

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
theorem _root_.solution {E : Finset (Cfg β)} : 0 < pr E ↔ E.Nonempty := by simp [pr]
end BSLambda.LLL
