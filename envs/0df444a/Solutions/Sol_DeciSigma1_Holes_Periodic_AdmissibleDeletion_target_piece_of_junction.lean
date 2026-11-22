-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.target_piece_of_junction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:31.789216+00:00
-- url     : https://prove2.me/submissions/e4af25d8-f1e8-4a7f-a06c-c9e1eebce55b

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_copy_piece
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_room
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_root
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_piecesOf
public import Theorems.Thm_DeciSigma1_Holes_Periodic_two_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
variable (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution (hN : 0 < N) {i j : Fin k} {ct ch : ℕ}
    (hcmp : SuffixComparison (editedTuple W ρ N x j) ct (editedTuple W ρ N x i) ch)
        (R : Piece W ρ.length)
    (hRl : R.coordinate = i) (hxR : x R ≠ 0) (h1 : ch < (hx.imagePiece R).start)
    (h2 : (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < ch +
        ((editedTuple W ρ N x j).length - ct)) :
    ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧ P' ∈
        piecesOf (editedTuple W ρ N x) ρ ∧
      P'.start = ct + ((hx.imagePiece R).start - ch) := by
  have hroom := hx.imagePiece_room hxR
  have h2d := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hd := (hx.imagePiece R).period_pos
  have hag : ∀ n < (editedTuple W ρ N x j).length - ct,
      (editedTuple W ρ N x i)[ch + n]? = (editedTuple W ρ N x j)[ct + n]? :=
    fun n hn => (hcmp n (by omega)).symm
  obtain ⟨P, hPl, hPs, hProot, _, _⟩ := copy_piece hag (hx.imagePiece R) hRl h1
    (ℓ := Periodic.boundaryMargin N ρ.length + 1) (by omega) (by omega) (by omega)
  refine ⟨P, hPl, ?_, hPs⟩
  rw [mem_piecesOf, hProot, hx.imagePiece_root]
  exact (mem_piecesOf _).mp (hx.supp R hxR)
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
