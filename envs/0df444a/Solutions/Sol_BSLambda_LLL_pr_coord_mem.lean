-- Prove2me | solution 1 for BSLambda.LLL.pr_coord_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:42.131197+00:00
-- url     : https://prove2.me/submissions/13631117-9974-433f-b01d-69dc50aa35a7

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
public import Theorems.Thm_BSLambda_LLL_pr_biUnion
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_pr_coord_eq
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
theorem _root_.solution (a : A) (s : Finset (β a)) :
    pr (Finset.univ.filter fun ω : Cfg β => ω a ∈ s)
      = (s.card : ℝ) / (Fintype.card (β a) : ℝ) := by
  have hU : (Finset.univ.filter fun ω : Cfg β ↦ ω a ∈ s)
      = s.biUnion (fun b ↦ Finset.univ.filter fun ω : Cfg β ↦ ω a = b) := by
    ext ω
    simp
  have hdisj : ∀ b ∈ s, ∀ c ∈ s, b ≠ c →
      Disjoint (Finset.univ.filter fun ω : Cfg β ↦ ω a = b)
        (Finset.univ.filter fun ω : Cfg β ↦ ω a = c) := fun b _ c _ hbc ↦
    Finset.disjoint_filter.2 fun ω _ h1 h2 ↦ hbc (h1 ▸ h2)
  rw [hU, pr_biUnion hdisj, Finset.sum_congr rfl fun b _ ↦ pr_coord_eq a b, Finset.sum_const,
    nsmul_eq_mul, mul_one_div]
end BSLambda.LLL
