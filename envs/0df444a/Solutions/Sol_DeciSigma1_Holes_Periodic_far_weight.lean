-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.far_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:01.028765+00:00
-- url     : https://prove2.me/submissions/dc88a33a-dd3a-4f17-9206-56351bd2a746

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {L Q K M : ℕ} {a b : ℤ} (hM : 0 < M) (hfar : L + K ≤ Q)
    (h : a - (((Q - L - K) / M : ℕ) : ℤ) ≤ b) :
    (L : ℤ) + M * a + K ≤ (Q : ℤ) + M * b := by
  have hd := Nat.mul_div_le (Q - L - K) M
  have hdZ : (M : ℤ) * ((Q - L - K) / M : ℕ) ≤ (Q - L - K : ℕ) := by
    exact_mod_cast hd
  have he : ((Q - L - K : ℕ) : ℤ) = (Q : ℤ) - L - K := by omega
  rw [he] at hdZ
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  nlinarith
end DeciSigma1.Holes.Periodic
