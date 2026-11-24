-- Prove2me | solution 1 for BSLambda.LLL.pr_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:45:09.55089+00:00
-- url     : https://prove2.me/submissions/fd86ce67-66d5-4ed3-a2d9-023120451117

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
theorem _root_.solution : pr (∅ : Finset (Cfg β)) = 0 := by simp [pr]
end BSLambda.LLL
