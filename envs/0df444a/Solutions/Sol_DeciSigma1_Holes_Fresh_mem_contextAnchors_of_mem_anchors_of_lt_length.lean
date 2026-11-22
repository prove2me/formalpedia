-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.mem_contextAnchors_of_mem_anchors_of_lt_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:58.735269+00:00
-- url     : https://prove2.me/submissions/c534873d-c172-4362-b7bb-a69b0321283f

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ} {l : Fin k}
    {p : ℕ}
    (hp : p ∈ anchors W t l) (hlt : p < (W l).length) : p ∈ contextAnchors W t (W l) := by
  rcases mem_insert.mp hp with h | h
  · omega
  · exact h
end DeciSigma1.Holes.Fresh
