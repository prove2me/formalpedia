-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.Event.reach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:10:47.26271+00:00
-- url     : https://prove2.me/submissions/564dbe7f-f7b9-41c3-b93a-210752e74cc1

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Closure_reach_of_cuts


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Reduction
namespace Event
theorem _root_.solution {a b : Closure.Config n V} (h : Event c Γ a b) : Reach c Γ a b := by
  obtain ⟨i, hi, j, hj, hp, hg⟩ := h
  exact reach_of_cuts hi hj hp hg
end Event
end DeciSigma1.Full.Reduction
