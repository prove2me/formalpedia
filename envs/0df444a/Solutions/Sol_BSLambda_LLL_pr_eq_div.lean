-- Prove2me | solution 1 for BSLambda.LLL.pr_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:49:09.85723+00:00
-- url     : https://prove2.me/submissions/4bbcee4a-f27f-4682-a0d9-f5bebf5acf6d

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
namespace BSLambda.LLL
theorem _root_.solution (E : Finset (Cfg β)) :
    pr E = (E.card : ℝ) / (Fintype.card (Cfg β) : ℝ) := Finset.nnratCast_dens E
end BSLambda.LLL
