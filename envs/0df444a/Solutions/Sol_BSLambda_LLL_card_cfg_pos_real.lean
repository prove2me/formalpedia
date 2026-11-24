-- Prove2me | solution 1 for BSLambda.LLL.card_cfg_pos_real
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:23.552825+00:00
-- url     : https://prove2.me/submissions/7a0f4487-47dd-4ee1-84aa-3eedf3b4a52b

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
variable [∀ a, Nonempty (β a)]


theorem solution : (0 : ℝ) < (Fintype.card (Cfg β) : ℝ) := by
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Cfg β))
