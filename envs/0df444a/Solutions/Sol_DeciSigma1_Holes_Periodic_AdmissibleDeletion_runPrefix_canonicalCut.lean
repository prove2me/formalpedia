-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_canonicalCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:48.368628+00:00
-- url     : https://prove2.me/submissions/c8f056f0-f147-46fd-8a7f-4b0aa412c4e8

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_editedTuple
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_deletedPositions_lt_length


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution [Fintype S] (T : Table α S k) (hN : N = Fintype.card S) {l : Fin k}
    {c c' : ℕ} (h :
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c') :
    T.runPrefix (editedTuple W ρ N x) l c' =
        T.runPrefix W l c := by
  rw [← h.2.1]
  apply hx.runPrefix_editedTuple T hN l h.1
  right; left
  intro hm
  exact (h.2.2 (hx.deletedPositions_lt_length hm)) hm
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
