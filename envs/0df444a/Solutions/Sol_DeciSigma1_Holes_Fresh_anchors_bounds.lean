-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.anchors_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:44:28.353191+00:00
-- url     : https://prove2.me/submissions/cd0d590a-cbe4-43c1-ad23-9c9ea8224c77

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_length_of_mem_anchors

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ} {l : Fin k} (hl : W l ≠ []) {p : ℕ}
    (hp : p ∈ anchors W t l) : 1 ≤ p ∧ p ≤ (W l).length := by
  refine ⟨?_, le_length_of_mem_anchors hp⟩
  rcases mem_insert.mp hp with rfl | hp
  · exact List.length_pos_iff.mpr hl
  · exact contextAnchors_pos hp
end DeciSigma1.Holes.Fresh
