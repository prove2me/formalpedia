-- Prove2me | solution 1 for BSLambda.LLL.disjoint_supp_sup_sdiff_nbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:13:12.128336+00:00
-- url     : https://prove2.me/submissions/53be2c45-402e-4bb6-ba78-7bf35b52cf2b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Theorems.Thm_BSLambda_LLL_mem_nbr
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ


attribute [local simp] BSLambda.LLL.mem_nbr

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [Fintype A]
namespace BSLambda.LLL
theorem _root_.solution {supp : I → Finset A} {i : I} {S : Finset I} (hi : i ∉ S) :
    Disjoint (supp i) ((S \ nbr supp i).sup supp) := by
  rw [Finset.disjoint_sup_right]
  intro j hj
  rw [Finset.mem_sdiff] at hj
  by_contra hc
  exact hj.2 (mem_nbr.mpr ⟨fun e ↦ hi (e ▸ hj.1), hc⟩)
end BSLambda.LLL
