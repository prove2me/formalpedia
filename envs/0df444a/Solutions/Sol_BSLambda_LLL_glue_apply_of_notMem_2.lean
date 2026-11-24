-- Prove2me | solution 2 for BSLambda.LLL.glue_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:47:36.912931+00:00
-- url     : https://prove2.me/submissions/46fe5323-eb22-4f7d-b3ef-264ad7ce6ff0

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
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ
attribute [local simp] BSLambda.LLL.glue_apply_of_mem

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
omit [Fintype A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution {S : Finset A} {u v : Cfg β} {a : A} (ha : a ∉ S) :
    glue S u v a = v a := by simp [glue, ha]
end BSLambda.LLL
