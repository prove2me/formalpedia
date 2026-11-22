-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.mem_contextAnchors_append_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:33.952612+00:00
-- url     : https://prove2.me/submissions/f2fd0e29-cc38-455c-b1d8-45e20f75c2d8

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_append_left
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {u v : List α} {e : ℕ} (he : e ≤ u.length) :
    e ∈ contextAnchors W t (u ++ v) ↔ e ∈ contextAnchors W t u := by
  refine ⟨fun h => ?_, contextAnchors_append_left⟩
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc, List.length_append] at h ⊢; omega
  · obtain ⟨-, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp h
    rw [List.take_append_of_le_length he] at hs
    exact (mem_contextAnchors_succ W).mpr ⟨he, m, hm, hs⟩
end DeciSigma1.Holes.Fresh
