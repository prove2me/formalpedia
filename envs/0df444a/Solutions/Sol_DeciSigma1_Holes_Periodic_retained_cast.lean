-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.retained_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:00:26.49611+00:00
-- url     : https://prove2.me/submissions/d0affd84-2f27-4626-b14f-1ddfe945bd19

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_floor_edit
public import Theorems.Thm_DeciSigma1_Holes_Periodic_deletionCounts_val

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
variable {N : ℕ} {z : {P // P ∈ piecesOf W ρ} → ℤ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (hf : ∀ P, shiftFloor N P.val ≤ z P) (hz0 : ∀ P, z P ≤ 0)
    (P : {P // P ∈ piecesOf W ρ}) :
    ((P.val.len - statePeriodModulus N ρ.length * deletionCounts z P.val : ℕ) : ℤ) =
      (P.val.len : ℤ) + statePeriodModulus N ρ.length * z P := by
  rw [deletionCounts_val]
  have hb := (floor_edit (hf P) (hz0 P)).1
  have hz : ((-z P).toNat : ℤ) = -z P := Int.toNat_of_nonneg (by have := hz0 P; omega)
  rw [Int.natCast_sub hb, Nat.cast_mul, hz]
  ring
end DeciSigma1.Holes.Periodic
