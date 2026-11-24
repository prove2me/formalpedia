-- Prove2me | solution 1 for BSLambda.LLL.Determined.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:27.328111+00:00
-- url     : https://prove2.me/submissions/b54dbe02-2a8e-494f-b9e1-845f96db709d

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
omit [Fintype A] [DecidableEq A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]
namespace BSLambda.LLL
namespace Determined
theorem _root_.solution {S T : Finset A} {E : Finset (Cfg β)} (hST : S ⊆ T)
    (hE : Determined S E) : Determined T E :=
  fun ω ω' h ↦ hE ω ω' fun a ha ↦ h a (hST ha)
end Determined
end BSLambda.LLL
