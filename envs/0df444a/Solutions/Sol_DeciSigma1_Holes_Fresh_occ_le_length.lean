-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.occ_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:37.139784+00:00
-- url     : https://prove2.me/submissions/cb7ce71a-34c5-44a1-a940-2ffa01bd9dc3

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
variable {x u v : List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {i : ℕ} (hu : u <+: x.drop i) (hne : u ≠ []) :
    i + u.length ≤ x.length := by
  have h1 := hu.length_le
  have h2 : 0 < u.length := List.length_pos_iff.mpr hne
  simp only [List.length_drop] at h1
  omega
end DeciSigma1.Holes.Fresh
