-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.anchorCount_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:11.153211+00:00
-- url     : https://prove2.me/submissions/aa0cc380-7a70-4f41-aa47-5d5226b071fb

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
theorem _root_.solution {p q e : ℕ} (h : q ≤ p) : anchorCount A p e ≤ anchorCount A q e :=
  card_le_card fun r hr => by
    simp only [mem_filter] at hr ⊢; exact ⟨hr.1, by omega, hr.2.2⟩
end DeciSigma1.Holes.Fresh
