-- Prove2me | solution 2 for Erdos77.uniform_binomial_entropy_log_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T16:25:22.409867+00:00
-- url     : https://prove2.me/submissions/ada3f9fe-4b0e-41e6-a718-d5165a6ea1de

import Mathlib
import Theorems.Thm_Erdos77_uniform_binomial_entropy_general_lower_bound

theorem solution :
  forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
    Real.exp ((((1 + ((ell : Real) / k) : Real) * Real.log (1 + ((ell : Real) / k)) -
      ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) -
      Real.log (2 * (k : Real) + 1)) <= (Nat.choose (k + ell) ell : Real) := by
  intro k ell hk hell hle
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hellR : (0 : Real) < (ell : Real) := by exact_mod_cast hell
  let x : Real := (ell : Real) / (k : Real)
  have hx : 0 < x := by dsimp [x]; positivity
  have hsum : ((k + ell : Nat) : Real) = (k : Real) * (1 + x) := by
    dsimp [x]
    push_cast
    field_simp
    <;> ring
  have hellEq : (ell : Real) = (k : Real) * x := by
    dsimp [x]
    field_simp
  have hlogsum : Real.log ((k + ell : Nat) : Real) =
      Real.log (k : Real) + Real.log (1 + x) := by
    rw [hsum, Real.log_mul (ne_of_gt hkR) (by positivity)]
  have hlogell : Real.log (ell : Real) =
      Real.log (k : Real) + Real.log x := by
    rw [hellEq, Real.log_mul (ne_of_gt hkR) (ne_of_gt hx)]
  have hEntropy :
      (((k + ell : Nat) : Real) * Real.log ((k + ell : Nat) : Real) -
        (k : Real) * Real.log (k : Real) -
        (ell : Real) * Real.log (ell : Real)) =
      ((1 + x) * Real.log (1 + x) - x * Real.log x) * (k : Real) := by
    rw [hlogsum, hlogell, hsum, hellEq]
    ring
  have hNat : k + ell + 1 ≤ 2 * k + 1 := by omega
  have hNatR : ((k + ell + 1 : Nat) : Real) ≤ 2 * (k : Real) + 1 := by
    exact_mod_cast hNat
  have hlog : Real.log ((k + ell + 1 : Nat) : Real) ≤
      Real.log (2 * (k : Real) + 1) :=
    Real.log_le_log (by positivity) hNatR
  have harg :
      (((1 + x) * Real.log (1 + x) - x * Real.log x) * (k : Real) -
        Real.log (2 * (k : Real) + 1)) ≤
      (((k + ell : Nat) : Real) * Real.log ((k + ell : Nat) : Real) -
        (k : Real) * Real.log (k : Real) -
        (ell : Real) * Real.log (ell : Real) -
        Real.log ((k + ell + 1 : Nat) : Real)) := by
    rw [← hEntropy]
    linarith
  calc
    _ ≤ Real.exp ((((k + ell : Nat) : Real) * Real.log ((k + ell : Nat) : Real) -
        (k : Real) * Real.log (k : Real) - (ell : Real) * Real.log (ell : Real)) -
        Real.log ((k + ell + 1 : Nat) : Real)) := Real.exp_le_exp.mpr harg
    _ ≤ (Nat.choose (k + ell) ell : Real) :=
      Erdos77.uniform_binomial_entropy_general_lower_bound k ell hk hell
