-- Prove2me | solution 1 for BSLambda.LLL.pr_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:22.603954+00:00
-- url     : https://prove2.me/submissions/f7126f78-6a76-401a-8274-c54c98cd80dd

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
omit [(a : A) → DecidableEq (β a)]


theorem solution (E : Finset (Cfg β)) : 0 ≤ pr E := by
  unfold pr; positivity
