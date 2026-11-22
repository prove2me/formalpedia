-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.anchorCount_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:04.540706+00:00
-- url     : https://prove2.me/submissions/0570b44e-32bc-4919-b52a-e7fd3fece2ed

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {A : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {s p e : ℕ} (h1 : s ≤ p) (h2 : p ≤ e) :
    anchorCount A s e = anchorCount A s p + anchorCount A p e := by
  unfold anchorCount
  rw [← card_union_of_disjoint]
  · congr 1
    ext q
    by_cases hq : q ∈ A
    · simp only [mem_filter, mem_union, hq, true_and]; omega
    · simp [hq]
  · rw [disjoint_left]
    intro q hq hq'
    simp only [mem_filter] at hq hq'
    omega
end DeciSigma1.Holes.Fresh
