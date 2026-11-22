-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Edge.commonSuffixLength_le_startDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:43:58.944617+00:00
-- url     : https://prove2.me/submissions/736d5f34-92f1-4ac7-942e-d4fdbc2723ff

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_commonSuffixLength_mem_trieNodes

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
open DeciSigma1.Holes.Fresh.Edge
variable {W : Fin k → List α} {t : ℕ} (e : Edge W t)
namespace DeciSigma1.Holes.Fresh.Edge
theorem _root_.solution {Y : List (List α)} (hY : Y ∈ upperParses W t)
    (h : commonSuffixLength e.blocks Y < e.endDepth) :
    commonSuffixLength e.blocks Y ≤ e.startDepth := by
  by_contra h'
  exact e.no_interior_node _ (commonSuffixLength_mem_trieNodes e.blocks hY) ⟨by omega, h⟩
end DeciSigma1.Holes.Fresh.Edge
