-- Prove2me | solution 2 for BSLambda.LLL.determined_pin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:53:20.985611+00:00
-- url     : https://prove2.me/submissions/77b5ec3b-4e0b-4e55-b4d9-d4b3b82aaf71

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_determined_filter_univ

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution (T : Finset A) (s : (a : A) → Finset (β a)) :
    Determined T (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a) :=
  determined_filter_univ _ fun _ _ hagree ↦
    forall₂_congr fun a ha ↦ by rw [hagree a ha]
end BSLambda.LLL
