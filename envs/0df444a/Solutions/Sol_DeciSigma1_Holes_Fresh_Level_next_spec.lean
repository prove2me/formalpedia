-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.next_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:00.185808+00:00
-- url     : https://prove2.me/submissions/217d1728-5438-45a1-8b1a-579f92a43a1c

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_lastInteriorCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_blockLengthAt_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}
namespace DeciSigma1.Holes.Fresh.Level
theorem _root_.solution {W : Fin k → List α} {l : Fin k} (hl : l ∈ (L.next W).active) :
    ∃ m ∈ L.active, L.marker m <:+ (W l).take (L.lastInteriorCut (W l)) ∧
      L.blockLengthAt (W l) (L.lastInteriorCut (W l)) = (L.marker m).length ∧
      (L.marker m).length ≤ L.lastInteriorCut (W l) ∧
      (L.next W).marker l = (W l).drop (L.lastInteriorCut (W l) - (L.marker m).length) ∧
      (L.next W).marker l = L.marker m ++ (W l).drop (L.lastInteriorCut (W l)) := by
  obtain ⟨-, hex⟩ := next_active.mp hl
  obtain ⟨he, hlt, -⟩ := lastInteriorCut_spec hex
  obtain ⟨m, hm, hs, hlen⟩ := blockLengthAt_spec he
  have hle : L.lastInteriorCut (W l) ≤ (W l).length := hlt.le
  obtain ⟨hl1, hocc⟩ := (suffix_take_iff hle).mp hs
  have hmk : (L.next W).marker l = (W l).drop (L.lastInteriorCut (W l) - (L.marker m).length) := by
    simp only [next, hlen]
  refine ⟨m, hm, hs, hlen, hl1, hmk, ?_⟩
  rw [hmk]
  obtain ⟨r, hr⟩ := hocc
  have hd := congrArg (List.drop (L.marker m).length) hr
  rw [List.drop_left, List.drop_drop, Nat.sub_add_cancel hl1] at hd
  rw [← hr, hd]
end DeciSigma1.Holes.Fresh.Level
