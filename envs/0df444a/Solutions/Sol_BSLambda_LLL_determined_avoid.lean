-- Prove2me | solution 1 for BSLambda.LLL.determined_avoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:48.016489+00:00
-- url     : https://prove2.me/submissions/3715c25a-410a-46ca-a845-570e6abdba02

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
theorem _root_.solution {Ev : I → Finset (Cfg β)} {supp : I → Finset A}
    (hdet : ∀ i, Determined (supp i) (Ev i)) (S : Finset I) :
    Determined (S.sup supp) (avoid Ev S) := fun ω ω' h ↦ by
  simp only [mem_avoid]
  exact forall₂_congr fun i hi ↦
    not_congr (hdet i ω ω' fun a ha ↦ h a (Finset.le_sup (f := supp) hi ha))
end BSLambda.LLL
