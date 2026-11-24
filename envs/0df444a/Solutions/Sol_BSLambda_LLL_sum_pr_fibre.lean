-- Prove2me | solution 1 for BSLambda.LLL.sum_pr_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:39.754949+00:00
-- url     : https://prove2.me/submissions/9256364c-a89a-4500-a76b-948eca5f074d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Theorems.Thm_BSLambda_LLL_mem_fibre_restrict
public import Theorems.Thm_BSLambda_LLL_disjoint_fibre
public import Theorems.Thm_BSLambda_LLL_pr_biUnion
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.pr_univ



set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {G : Finset A}
namespace BSLambda.LLL
theorem _root_.solution (G : Finset A) :
    ∑ c ∈ G.pi fun a ↦ (Finset.univ : Finset (β a)), pr (fibre G c) = 1 := by
  have hcover : (G.pi fun a ↦ (Finset.univ : Finset (β a))).biUnion (fibre G)
      = (Finset.univ : Finset (Cfg β)) :=
    Finset.eq_univ_of_forall fun ω ↦ Finset.mem_biUnion.mpr
      ⟨fun a _ ↦ ω a, Finset.mem_pi.mpr fun a _ ↦ Finset.mem_univ _, mem_fibre_restrict ω⟩
  rw [← pr_biUnion fun c _ c' _ hne ↦ disjoint_fibre hne, hcover, pr_univ]
end BSLambda.LLL
