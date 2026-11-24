-- Prove2me | solution 1 for BSLambda.LLL.pr_coord_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:13:22.073837+00:00
-- url     : https://prove2.me/submissions/0405decb-ff6c-423f-b19b-661c92c3c5ed

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_eq_div
public import Theorems.Thm_BSLambda_LLL_card_cfg_pos_real
public import Theorems.Thm_BSLambda_LLL_card_filter_coord_mul_card

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
variable [∀ a, Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution (a : A) (b : β a) :
    pr (Finset.univ.filter fun ω : Cfg β => ω a = b) = 1 / (Fintype.card (β a) : ℝ) := by
  rw [pr_eq_div, div_eq_div_iff card_cfg_pos_real.ne'
    (Nat.cast_ne_zero.mpr (Fintype.card_pos (α := β a)).ne'), one_mul]
  exact_mod_cast card_filter_coord_mul_card a b
end BSLambda.LLL
