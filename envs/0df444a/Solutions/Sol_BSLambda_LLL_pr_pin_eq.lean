-- Prove2me | solution 1 for BSLambda.LLL.pr_pin_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:18.648752+00:00
-- url     : https://prove2.me/submissions/ccf88a02-bfda-482d-a8c7-d648537f8ac1

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
public import Theorems.Thm_BSLambda_LLL_determined_coord
public import Theorems.Thm_BSLambda_LLL_determined_pin
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_pr_inter_of_disjoint_support
public import Theorems.Thm_BSLambda_LLL_pr_coord_mem
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
variable [∀ a, Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution (T : Finset A) (s : (a : A) → Finset (β a)) :
    pr (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a)
      = ∏ a ∈ T, ((s a).card : ℝ) / (Fintype.card (β a) : ℝ) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have heq : (Finset.univ.filter fun ω : Cfg β ↦ ∀ b ∈ insert a T, ω b ∈ s b) =
        (Finset.univ.filter fun ω : Cfg β ↦ ω a ∈ s a) ∩
        (Finset.univ.filter fun ω : Cfg β ↦ ∀ b ∈ T, ω b ∈ s b) := by
      ext ω
      simp
    have hdisj : Disjoint {a} T := by simp [ha]
    rw [heq, pr_inter_of_disjoint_support (determined_coord a (s a)) (determined_pin T s) hdisj,
      pr_coord_mem, ih, Finset.prod_insert ha]
end BSLambda.LLL
