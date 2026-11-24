-- Prove2me | solution 1 for BSLambda.LLL.determined_filter_univ
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:50:22.725803+00:00
-- url     : https://prove2.me/submissions/9e9dc2cf-a24f-4028-94ae-33440c298d34

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


theorem solution {S : Finset A} (p : Cfg β → Prop) [DecidablePred p]
    (hp : ∀ ω ω' : Cfg β, (∀ a ∈ S, ω a = ω' a) → (p ω ↔ p ω')) :
    Determined S (Finset.univ.filter p) := by
  intro u v h; simpa using hp u v h
