-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.least_shifts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:59.834272+00:00
-- url     : https://prove2.me/submissions/91f6fccc-d26a-4abd-be71-e7451efaa2c2

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_shiftSystem_zero
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_least_above


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (N : ℕ) :
    ∃ z : {P // P ∈ piecesOf W ρ} → ℤ,
      (shiftSystem W ρ N).Sat z ∧ (∀ P, shiftFloor N P.val ≤ z P) ∧
      (∀ y, (shiftSystem W ρ N).Sat y → (∀ P, shiftFloor N P.val ≤ y P) → z ≤ y) ∧
      (∀ P, z P ≤ 0) ∧
      ∀ P, ∃ p : List {P // P ∈ piecesOf W ρ}, p.Nodup ∧ p.getLast? = some P ∧
        (∃ Q, p.head? = some Q ∧ z Q = shiftFloor N Q.val) ∧
        p.IsChain ((shiftSystem W ρ N).IsTight z) := by
  have hf : (fun P : {P // P ∈ piecesOf W ρ} => shiftFloor N P.val) ≤ (fun _ => 0) := by
    intro P; exact neg_nonpos.mpr (Int.natCast_nonneg _)
  obtain ⟨z, hz, hfloor, hleast, hpath⟩ :=
    (shiftSystem W ρ N).least_above _ _ (shiftSystem_zero N) hf
  exact ⟨z, hz, hfloor, hleast, hleast _ (shiftSystem_zero N) hf, hpath⟩
end DeciSigma1.Holes.Periodic
