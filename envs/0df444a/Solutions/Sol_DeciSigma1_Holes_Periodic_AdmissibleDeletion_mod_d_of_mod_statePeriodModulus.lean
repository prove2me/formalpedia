-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.mod_d_of_mod_statePeriodModulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:47.087048+00:00
-- url     : https://prove2.me/submissions/e4e6cc69-6d0d-4cac-9802-d3af28063f79

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport

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
omit hx
omit [DecidableEq α]
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution {a b : ℕ} (h : SameStatePhase N ρ.length a b) :
    a % ρ.length = b % ρ.length := by
  rcases h with h | ⟨_, _, h⟩
  · rw [h]
  · have hd : ρ.length ∣ Periodic.statePeriodModulus N ρ.length := ⟨_, rfl⟩
    rw [← Nat.mod_mod_of_dvd a hd, ← Nat.mod_mod_of_dvd b hd, h]
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
