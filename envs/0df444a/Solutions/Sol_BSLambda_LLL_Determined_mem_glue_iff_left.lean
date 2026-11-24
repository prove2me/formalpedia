-- Prove2me | solution 1 for BSLambda.LLL.Determined.mem_glue_iff_left
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:54:48.650525+00:00
-- url     : https://prove2.me/submissions/023d39d0-ac7d-4871-a666-6712c3673085

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


theorem solution {S : Finset A} {E : Finset (Cfg β)} (hE : Determined S E)
    {u v : Cfg β} : glue S u v ∈ E ↔ u ∈ E := by
  apply hE
  intro a ha
  simp [glue,ha]
