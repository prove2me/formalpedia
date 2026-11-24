-- Prove2me | solution 1 for BSLambda.LLL.glue_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:47:07.326268+00:00
-- url     : https://prove2.me/submissions/58ed1357-fd6a-44a9-a8f6-6a1c8399dfda

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
omit [Fintype A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]


theorem solution {S : Finset A} {u v : Cfg β} {a : A} (ha : a ∉ S) :
    glue S u v a = v a := by
  simp [glue, ha]
