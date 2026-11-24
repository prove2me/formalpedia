-- Prove2me | solution 2 for BSLambda.LLL.mem_nbr
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:48:27.272249+00:00
-- url     : https://prove2.me/submissions/67ce724e-6cdc-4b2c-ab3c-d37c305af62f

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
omit [Fintype A]


theorem solution {supp : I → Finset A} {i j : I} :
    j ∈ nbr supp i ↔ j ≠ i ∧ ¬ Disjoint (supp i) (supp j) := by
  simp [nbr]
