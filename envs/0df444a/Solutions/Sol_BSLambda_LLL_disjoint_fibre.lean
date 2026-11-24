-- Prove2me | solution 1 for BSLambda.LLL.disjoint_fibre
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:54:45.363123+00:00
-- url     : https://prove2.me/submissions/1025a194-3f25-49c6-b454-26d65f806ce6

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


theorem solution {c c' : (a : A) → a ∈ G → β a} (h : c ≠ c') :
    Disjoint (fibre G c) (fibre G c') := by
  apply Finset.disjoint_left.mpr
  intro ω h₁ h₂
  have h₁' : ∀ a, ∀ ha : a ∈ G, ω a = c a ha := by simpa [fibre] using h₁
  have h₂' : ∀ a, ∀ ha : a ∈ G, ω a = c' a ha := by simpa [fibre] using h₂
  exact h (funext fun a => funext fun ha => (h₁' a ha).symm.trans (h₂' a ha))
