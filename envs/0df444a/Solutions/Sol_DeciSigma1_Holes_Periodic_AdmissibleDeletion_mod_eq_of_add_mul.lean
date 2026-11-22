-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.mod_eq_of_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:46.587178+00:00
-- url     : https://prove2.me/submissions/9b56c48e-0a6c-4e6f-80ea-3310adff89b4

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
omit [DecidableEq α] hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution {a b u v M : ℕ} (h : a + M * u = b + M * v) : a % M = b % M := by
  have h1 : (a + M * u) % M = a % M := Nat.add_mul_mod_self_left a M u
  have h2 : (b + M * v) % M = b % M := Nat.add_mul_mod_self_left b M v
  rw [← h1, ← h2, h]
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
