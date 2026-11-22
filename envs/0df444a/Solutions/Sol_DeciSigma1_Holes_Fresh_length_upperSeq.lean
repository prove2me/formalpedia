-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.length_upperSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:44:02.558098+00:00
-- url     : https://prove2.me/submissions/d1d88ec3-b913-45c3-81dc-651773451993

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
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


attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) :
    (upperParse W t o).length = lowerBlockCount W t o := by simp [upperParse]
end DeciSigma1.Holes.Fresh
