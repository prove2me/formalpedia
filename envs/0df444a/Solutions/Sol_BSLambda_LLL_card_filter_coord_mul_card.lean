-- Prove2me | solution 1 for BSLambda.LLL.card_filter_coord_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:53.650797+00:00
-- url     : https://prove2.me/submissions/5ba893e8-535d-4349-b159-84eef035f8cd

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution (a : A) (b : β a) :
    (Finset.univ.filter fun ω : Cfg β => ω a = b).card * Fintype.card (β a)
      = Fintype.card (Cfg β) := by
  have h := Fintype.card_filter_piFinset_eq_of_mem
    (fun i ↦ (Finset.univ : Finset (β i))) a (Finset.mem_univ b)
  simp only [Fintype.piFinset_univ, Finset.card_univ] at h
  rw [h, Fintype.card_pi]
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ a)
end BSLambda.LLL
