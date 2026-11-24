-- Prove2me | solution 2 for BSLambda.LLL.determined_filter_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:50:54.505273+00:00
-- url     : https://prove2.me/submissions/09844628-8cb8-4829-9fac-e7a4b7e076df

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
omit [(a : A) → DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution {S : Finset A} (p : Cfg β → Prop) [DecidablePred p]
    (hp : ∀ ω ω' : Cfg β, (∀ a ∈ S, ω a = ω' a) → (p ω ↔ p ω')) :
    Determined S (Finset.univ.filter p) := fun ω ω' h ↦ by simpa using hp ω ω' h
end BSLambda.LLL
