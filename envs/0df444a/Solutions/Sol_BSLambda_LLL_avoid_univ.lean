-- Prove2me | solution 1 for BSLambda.LLL.avoid_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:13:13.456944+00:00
-- url     : https://prove2.me/submissions/053a3dad-f6b6-4145-8dd8-98f5ed819e63

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Theorems.Thm_BSLambda_LLL_mem_nbr
public import Theorems.Thm_BSLambda_LLL_mem_avoid
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ


attribute [local simp] BSLambda.LLL.mem_nbr
attribute [local simp] BSLambda.LLL.mem_avoid
attribute [local simp] BSLambda.LLL.avoid_empty

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [∀ (a : A), Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution (Ev : I → Finset (Cfg β)) :
    avoid Ev (Finset.univ : Finset I) = Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i := by
  ext ω
  simp
end BSLambda.LLL
