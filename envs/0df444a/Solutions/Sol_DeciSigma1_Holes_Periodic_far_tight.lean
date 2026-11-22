-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.far_tight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:03.863313+00:00
-- url     : https://prove2.me/submissions/4afbd62c-1670-4432-956d-dac1730b259a

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
    (h : a - (((Q - L - K) / M : ℕ) : ℤ) = b) :
    (Q : ℤ) + M * b < (L : ℤ) + M * a + K + M := by
  have hr := Nat.mod_lt (Q - L - K) hM
  have he := Nat.mod_add_div (Q - L - K) M
  have heZ : (((Q - L - K) % M : ℕ) : ℤ) + (M : ℤ) * ((Q - L - K) / M : ℕ) =
      (Q - L - K : ℕ) := by exact_mod_cast he
  have hsub : ((Q - L - K : ℕ) : ℤ) = (Q : ℤ) - L - K := by omega
  have hrZ : (((Q - L - K) % M : ℕ) : ℤ) < M := by exact_mod_cast hr
  rw [hsub] at heZ
  nlinarith
end DeciSigma1.Holes.Periodic
