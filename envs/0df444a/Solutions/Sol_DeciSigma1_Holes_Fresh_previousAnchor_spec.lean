-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.previousAnchor_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:34.712709+00:00
-- url     : https://prove2.me/submissions/d5cfa900-9f34-47e3-8d80-5bb7d41eaf3d

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
theorem _root_.solution {p : ℕ} (h : ∃ q ∈ A, q < p) :
    previousAnchor A p ∈ A ∧ previousAnchor A p < p := by
  have hne : (A.filter (· < p)).Nonempty := by
    obtain ⟨q, hq, hqp⟩ := h; exact ⟨q, mem_filter.mpr ⟨hq, hqp⟩⟩
  obtain ⟨q, hq, hsup⟩ := exists_mem_eq_sup _ hne id
  rw [mem_filter] at hq
  simp only [previousAnchor, hsup, id]
  exact hq
end DeciSigma1.Holes.Fresh
