-- Prove2me | solution 1 for BSLambda.LLL.avoid_anti
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:54:47.070326+00:00
-- url     : https://prove2.me/submissions/fcc60f7d-3221-4e50-ba5b-5da89fe74cdf

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


theorem solution {Ev : I → Finset (Cfg β)} {S T : Finset I} (h : S ⊆ T) :
    avoid Ev T ⊆ avoid Ev S := by
  intro ω hω
  simp only [avoid,Finset.mem_filter,Finset.mem_univ,true_and] at *
  exact fun i hi => hω i (h hi)
