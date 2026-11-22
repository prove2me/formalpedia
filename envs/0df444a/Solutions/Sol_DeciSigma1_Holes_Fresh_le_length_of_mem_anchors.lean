-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.le_length_of_mem_anchors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:51.199482+00:00
-- url     : https://prove2.me/submissions/caf31c81-5106-4126-b5fa-996be9031bc0

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_le_length

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ} {l : Fin k} {p : ℕ}
    (hp : p ∈ anchors W t l) : p ≤ (W l).length := by
  rcases mem_insert.mp hp with rfl | hp
  · exact le_rfl
  · exact contextAnchors_le_length hp
end DeciSigma1.Holes.Fresh
