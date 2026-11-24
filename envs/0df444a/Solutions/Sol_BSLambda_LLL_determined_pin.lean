-- Prove2me | solution 1 for BSLambda.LLL.determined_pin
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:20.6042+00:00
-- url     : https://prove2.me/submissions/2a985c3f-68e7-42c0-8ceb-8fab9ed8f410

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


theorem solution (T : Finset A) (s : (a : A) → Finset (β a)) :
    Determined T (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a) := by
  intro u v h; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hu a ha => h a ha ▸ hu a ha, fun hv a ha => (h a ha).symm ▸ hv a ha⟩
