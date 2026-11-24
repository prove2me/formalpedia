-- Prove2me | solution 1 for BSLambda.LLL.determined_fibre
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:54:46.206012+00:00
-- url     : https://prove2.me/submissions/91c90822-c710-4d50-bd89-73309251b01a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {G : Finset A}
omit [∀ (a : A), Nonempty (β a)]


theorem solution (c : (a : A) → a ∈ G → β a) : Determined G (fibre G c) := by
  intro u v h
  simp only [fibre,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun hu a ha => (h a ha).symm.trans (hu a ha), fun hv a ha => (h a ha).trans (hv a ha)⟩
