-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.followerEdge_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:48.407555+00:00
-- url     : https://prove2.me/submissions/025b5aa9-3fe5-4eb9-8435-5154a6da7ddf

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


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
theorem _root_.solution {P Q : Piece W ρ.length} (hP : P ∈ piecesOf W ρ) (hQ : Q ∈ piecesOf W ρ)
    (hG : FollowerEdge P Q) : x P = x Q ∨
      (P.len + Periodic.comparisonGap N ρ.length ≤ Q.len ∧
        retainedLength (N := N) (x := x) P + Periodic.comparisonGap N ρ.length ≤ retainedLength
            (N := N) (x := x) Q) ∨
      (Q.len + Periodic.comparisonGap N ρ.length ≤ P.len ∧
        retainedLength (N := N) (x := x) Q + Periodic.comparisonGap N ρ.length ≤ retainedLength
            (N := N) (x := x) P) := by
  by_cases h1 : P.len + Periodic.comparisonGap N ρ.length ≤ Q.len
  · right; left; exact ⟨h1, by have := hx.far P hP Q hQ hG h1; unfold retainedLength; omega⟩
  by_cases h2 : Q.len + Periodic.comparisonGap N ρ.length ≤ P.len
  · right; right; exact ⟨h2, by have := hx.far Q hQ P hP hG.symm h2; unfold retainedLength; omega⟩
  left; exact hx.near P hP Q hQ hG (by omega) (by omega)
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
