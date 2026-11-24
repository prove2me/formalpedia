-- Prove2me | solution 1 for BSLambda.LLL.avoid_empty
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:48:24.976686+00:00
-- url     : https://prove2.me/submissions/0482d76c-f06a-4f73-9bce-43723bf22b5a

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
omit [∀ (a : A), Nonempty (β a)]


theorem solution (Ev : I → Finset (Cfg β)) :
    avoid Ev ∅ = (Finset.univ : Finset (Cfg β)) := by
  ext; simp [avoid]
