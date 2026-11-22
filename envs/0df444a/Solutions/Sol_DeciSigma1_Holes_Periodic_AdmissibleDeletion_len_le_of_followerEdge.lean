-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.len_le_of_followerEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:48:42.281139+00:00
-- url     : https://prove2.me/submissions/92ce361b-f75b-4076-a276-e9de625fd9c2

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_len_eq_retainedLength_add
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_comparisonGap_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_followerEdge_cases

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
theorem _root_.solution {P Q : Piece W ρ.length} (hP : P ∈ piecesOf W ρ)
    (hQ : Q ∈ piecesOf W ρ)
    (hG : FollowerEdge P Q)
        (hle : retainedLength (N := N) (x := x) P ≤ retainedLength (N := N) (x := x) Q) :
    P.len ≤ Q.len := by
  have := comparisonGap_pos (N := N) P
  rcases hx.followerEdge_cases hP hQ hG with h | h | h
  · rw [hx.len_eq_retainedLength_add P, hx.len_eq_retainedLength_add Q, h]; omega
  · omega
  · omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
