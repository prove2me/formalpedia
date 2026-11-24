-- Prove2me | solution 2 for BSLambda.LLL.determined_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:00.67774+00:00
-- url     : https://prove2.me/submissions/a913d89f-7ea0-42f5-80d8-2d4802cebe59

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Theorems.Thm_BSLambda_LLL_determined_filter_univ


set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {G : Finset A}
omit [∀ (a : A), Nonempty (β a)]
namespace BSLambda.LLL
theorem _root_.solution (c : (a : A) → a ∈ G → β a) : Determined G (fibre G c) :=
  determined_filter_univ _ fun _ _ h ↦
    forall_congr' fun a ↦ forall_congr' fun ha ↦ by rw [h a ha]
end BSLambda.LLL
