-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.IsHole.of_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:17.299628+00:00
-- url     : https://prove2.me/submissions/854fd4c5-4c17-485a-a24a-d68abfc60e31

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_visitedStates
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_mem_visitedStates

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
open DeciSigma1.Readers.StructuralReader
variable (M : StructuralReader α S k)
variable {M}
namespace DeciSigma1.Readers.StructuralReader
namespace IsHole
theorem _root_.solution [DecidableEq α] [DecidableEq S] {U W : Fin k → List α}
    (hW : M.IsHole W) (hU : Dominates M.toTable U W) :
    M.IsHole U ∧ ∀ i, M.endState U i = M.endState W i := by
  refine ⟨⟨fun i => ⟨fun a ha => ?_, ?_⟩, fun i j pq hpq => ?_⟩, hU.endState_eq⟩
  · obtain ⟨b, hb, hq⟩ :=
      mem_visitedStates.mp (hU.visitedStates_subset i (runPrefix_mem_visitedStates U i ha))
    rw [← hq]; exact (hW.1 i).1 b hb
  · rw [hU.endState_eq i]; exact (hW.1 i).2
  · exact hW.2 i j pq (hU.channel_subset i j hpq)
end IsHole
end DeciSigma1.Readers.StructuralReader
