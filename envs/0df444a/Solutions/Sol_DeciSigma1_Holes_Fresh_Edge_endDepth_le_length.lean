-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Edge.endDepth_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:44:32.73208+00:00
-- url     : https://prove2.me/submissions/8b167e4b-a7db-4f6f-a7c9-2aa1f45cb8b4

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_length_of_mem_trieNodes

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
open DeciSigma1.Holes.Fresh.Edge
variable {W : Fin k → List α} {t : ℕ} (e : Edge W t)
namespace DeciSigma1.Holes.Fresh.Edge
theorem _root_.solution :
    e.endDepth ≤ e.blocks.length := le_length_of_mem_trieNodes e.endDepth_mem
end DeciSigma1.Holes.Fresh.Edge
