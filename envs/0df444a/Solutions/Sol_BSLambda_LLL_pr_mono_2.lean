-- Prove2me | solution 2 for BSLambda.LLL.pr_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:53:07.123695+00:00
-- url     : https://prove2.me/submissions/7e48fbaf-62a8-41cc-abfe-9d7e9eab8517

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
theorem _root_.solution {E F : Finset (Cfg β)} (h : E ⊆ F) : pr E ≤ pr F := by
  simpa [pr] using Finset.dens_le_dens h
end BSLambda.LLL
