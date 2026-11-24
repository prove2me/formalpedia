-- Prove2me | solution 1 for BSLambda.LLL.mem_fibre_restrict
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:21.857147+00:00
-- url     : https://prove2.me/submissions/cc1395f2-a3fb-4641-b482-539886f359ad

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


theorem solution (ω : Cfg β) : ω ∈ fibre G fun a _ ↦ ω a := by
  simp [fibre]
