-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.lastInteriorCut_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:27.875797+00:00
-- url     : https://prove2.me/submissions/ef7f7bb1-76c3-485f-b451-ff7f9662d818

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
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
theorem _root_.solution {x : List α} (h : ∃ e ∈ L.markerEndCuts x, e < x.length) :
    L.lastInteriorCut x ∈ L.markerEndCuts x ∧ L.lastInteriorCut x < x.length ∧
      ∀ e ∈ L.markerEndCuts x, e < x.length → e ≤ L.lastInteriorCut x := by
  have hne : ((L.markerEndCuts x).filter (· < x.length)).Nonempty := by
    obtain ⟨e, he, hlt⟩ := h
    exact ⟨e, mem_filter.mpr ⟨he, hlt⟩⟩
  obtain ⟨e0, he0, hsup⟩ := exists_mem_eq_sup _ hne id
  rw [mem_filter] at he0
  refine ⟨?_, ?_, ?_⟩
  · simp only [lastInteriorCut, hsup, id]; exact he0.1
  · simp only [lastInteriorCut, hsup, id]; exact he0.2
  · intro e he hlt
    exact le_sup (f := id) (mem_filter.mpr ⟨he, hlt⟩)
end DeciSigma1.Holes.Fresh.Level
