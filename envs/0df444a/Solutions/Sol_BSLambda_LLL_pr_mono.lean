-- Prove2me | solution 1 for BSLambda.LLL.pr_mono
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:23.404716+00:00
-- url     : https://prove2.me/submissions/8289db9e-f772-440d-990b-9d1f636ad9f6

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


theorem solution {E F : Finset (Cfg β)} (h : E ⊆ F) : pr E ≤ pr F := by
  unfold pr
  first | exact_mod_cast Finset.dens_le_dens h | unfold Finset.dens; gcongr; exact Finset.card_le_card h
