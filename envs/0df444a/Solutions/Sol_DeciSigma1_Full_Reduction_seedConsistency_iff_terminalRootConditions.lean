-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.seedConsistency_iff_terminalRootConditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:10.320748+00:00
-- url     : https://prove2.me/submissions/78217966-6dee-46a5-9ec5-e81c108c8730

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Reduction_collision_iff_events
public import Theorems.Thm_DeciSigma1_Full_Reduction_not_hasUnaryObstruction_iff
public import Theorems.Thm_DeciSigma1_Full_Reduction_self_iff_event

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution (A B : Fin k → Closure.Config n V) :
    SeedConsistency c Γ A B ↔ TerminalRootConditions c Γ A B := by
  constructor
  · rintro ⟨hL, hM, hE, hC⟩
    refine ⟨fun i => ((not_hasUnaryObstruction_iff (A i)).mp (hL i).1).1,
      fun i => ⟨hM i, ((not_hasUnaryObstruction_iff (A i)).mp (hL i).1).2⟩, ?_⟩
    intro j i
    refine ⟨hE j i, ?_⟩
    by_cases hji : j = i
    · subst j
      exact fun h => (hL i).2 ((self_iff_event (A i)).mp h)
    · exact fun h => hC j i hji ((collision_iff_events (A j) (A i)).mpr (Or.inl h))
  · rintro ⟨hP, hM, hE⟩
    refine ⟨fun i => ⟨(not_hasUnaryObstruction_iff (A i)).mpr ⟨hP i, (hM i).2⟩,
      fun h => (hE i i).2 ((self_iff_event (A i)).mpr h)⟩,
      fun i => (hM i).1, fun j i => (hE j i).1, ?_⟩
    intro j i _ h
    rcases (collision_iff_events (A j) (A i)).mp h with h | h
    · exact (hE j i).2 h
    · exact (hE i j).2 h
end DeciSigma1.Full.Reduction
