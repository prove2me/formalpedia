-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.Piece.runPrefix_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:43.451822+00:00
-- url     : https://prove2.me/submissions/f63a25eb-ed07-4f0d-8207-3ffddc64b9c3

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_runPrefix_add_mul
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Periodic
namespace Piece
theorem _root_.solution [Fintype S] (T : Table α S k) {d : ℕ} (P : Piece W d) {o₁ o₂ : ℕ}
    (h₁ : Periodic.stateTransientLength (Fintype.card S) d ≤ o₁)
        (h₂ : Periodic.stateTransientLength (Fintype.card S) d ≤ o₂)
    (h₁' : o₁ ≤ P.len) (h₂' : o₂ ≤ P.len)
        (hmod : o₁ % Periodic.statePeriodModulus (Fintype.card S) d =
      o₂ % Periodic.statePeriodModulus (Fintype.card S) d) :
    T.runPrefix W P.coordinate (P.start + o₁) = T.runPrefix W P.coordinate (P.start + o₂) := by
  unfold Periodic.stateTransientLength at h₁ h₂
  unfold Periodic.statePeriodModulus at hmod
  rcases le_total o₁ o₂ with h | h
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' h).mp hmod
    rw [show o₂ = o₁ + m * (d * (Fintype.card S).factorial) by rw [mul_comm m]; omega,
      ← Nat.add_assoc, P.runPrefix_add_mul T h₁ (by rw [mul_comm m]; omega)]
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' h).mp hmod.symm
    rw [show o₁ = o₂ + m * (d * (Fintype.card S).factorial) by rw [mul_comm m]; omega,
      ← Nat.add_assoc, P.runPrefix_add_mul T h₂ (by rw [mul_comm m]; omega)]
end Piece
end DeciSigma1.Holes.Periodic
