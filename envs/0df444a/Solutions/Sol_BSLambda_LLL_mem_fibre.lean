-- Prove2me | solution 1 for BSLambda.LLL.mem_fibre
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:48:21.85584+00:00
-- url     : https://prove2.me/submissions/7ba82b6d-c5cf-4b1a-afe4-d557e8cb97aa

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


theorem solution {c : (a : A) → a ∈ G → β a} {ω : Cfg β} :
    ω ∈ fibre G c ↔ ∀ a, ∀ ha : a ∈ G, ω a = c a ha := by
  simp [fibre]
