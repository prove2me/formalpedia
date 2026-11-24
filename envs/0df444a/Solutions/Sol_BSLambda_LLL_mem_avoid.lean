-- Prove2me | solution 1 for BSLambda.LLL.mem_avoid
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:48:26.341439+00:00
-- url     : https://prove2.me/submissions/0fec3012-5c6d-470f-8b04-b0afb332a265

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


theorem solution {Ev : I → Finset (Cfg β)} {S : Finset I} {ω : Cfg β} :
    ω ∈ avoid Ev S ↔ ∀ i ∈ S, ω ∉ Ev i := by
  simp [avoid]
