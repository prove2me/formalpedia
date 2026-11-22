-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.not_mem_of_canonicalCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:22.294806+00:00
-- url     : https://prove2.me/submissions/9ed0644d-094d-431f-9fbc-48933a483cfe

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_eq_greatestPreimage
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_keepCut_of_mem
public import Theorems.Thm_DeciSigma1_Words_not_mem_of_no_junction


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
    (hJ : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n)) :
    ∀ i < n, c + i ∉ deletedPositions W ρ N x l := by
  rw [← hx.canonicalCut_eq_greatestPreimage hc]
  refine not_mem_of_no_junction fun p hp h => ?_
  obtain ⟨R, hRl, hxR, hR⟩ := hx.keepCut_of_mem hp
  exact hJ R hRl hxR (hR ▸ h)
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
