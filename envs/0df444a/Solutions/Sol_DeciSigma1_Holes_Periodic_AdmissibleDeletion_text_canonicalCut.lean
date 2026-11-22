-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.text_canonicalCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:18.29092+00:00
-- url     : https://prove2.me/submissions/2486e564-43f7-4de6-b5ed-656c919ec309

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_not_mem_of_canonicalCut
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono
public import Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d


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
theorem _root_.solution {l : Fin k} {c c' n : ℕ} (hc :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c')
    (hn : c' + n ≤ (editedTuple W ρ N x l).length)
    (hJ : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n)) :
    (∀ i < n, c + i ∉ deletedPositions W ρ N x l ∧ c + i < (W l).length) ∧
      keepCut W ρ N x l (c + n) = c' + n ∧
      ∀ i < n, (W l)[c + i]? = (editedTuple W ρ N x l)[c' + i]? := by
  have hret := hx.not_mem_of_canonicalCut hc hJ
  have hck : retainedCount (deletedPositions W ρ N x l) c = c' := hc.2.1
  have hk : ∀ i ≤ n, retainedCount (deletedPositions W ρ N x l) (c + i) = c' + i := fun i hi => by
    rw [retainedCount_add_of_not_mem fun j hj => hret j (by omega), hck]
  have hlt : ∀ i < n, c + i < (W l).length := fun i hi => by
    by_contra hge
    have := retainedCount_mono (D := deletedPositions W ρ N x l) (Nat.le_of_not_lt hge)
    have := hk i hi.le
    rw [editedTuple, length_deletePositions] at hn
    omega
  refine ⟨fun i hi => ⟨hret i hi, hlt i hi⟩, hk n le_rfl, fun i hi => ?_⟩
  rw [← hk i hi.le]
  exact (getElem?_deletePositions _ (hret i hi) (hlt i hi)).symm
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
