-- Prove2me | solution 2 for Erdos77.binomial_entropy_log_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:13:32.040876+00:00
-- url     : https://prove2.me/submissions/85c952e0-84da-43aa-b919-7ded731919ed

import Mathlib
import Theorems.Thm_Erdos77_binomial_mean_mass_lower_bound
open Filter Topology

theorem solution (n r : Nat) (hr : 0 < r) (hrn : r < n) :
  Real.exp ((n : Real) * Real.log (n : Real) - (r : Real) * Real.log (r : Real) -
    (Nat.cast (n - r) : Real) * Real.log (Nat.cast (n - r) : Real) -
    Real.log ((n + 1 : Nat) : Real)) <= (Nat.choose n r : Real) := by
  let p : Real := (r : Real) / (n : Real)
  let q : Real := (Nat.cast (n - r) : Real) / (n : Real)
  have hn : (0 : Real) < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hsNat : 0 < n - r := by omega
  have hsR : (0 : Real) < (Nat.cast (n - r) : Real) := by exact_mod_cast hsNat
  have hn1 : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hprod : 0 < p ^ r * q ^ (n - r) := by positivity
  have hmass := Erdos77.binomial_mean_mass_lower_bound n r hr hrn
  have hmass' : (1 : Real) / ((n + 1 : Nat) : Real) / (p ^ r * q ^ (n - r)) <=
      (Nat.choose n r : Real) := by
    apply (div_le_iff₀ hprod).2
    simpa [p, q, mul_assoc] using hmass
  have hleftpos : 0 < (1 : Real) / ((n + 1 : Nat) : Real) / (p ^ r * q ^ (n - r)) := by positivity
  have hchoosepos : 0 < (Nat.choose n r : Real) := by
    exact_mod_cast Nat.choose_pos (le_of_lt hrn)
  have hlog := Real.log_le_log hleftpos hmass'
  have hsumR : (r : Real) + (Nat.cast (n - r) : Real) = (n : Real) := by
    exact_mod_cast Nat.add_sub_of_le (le_of_lt hrn)
  have hlogid :
      Real.log ((1 : Real) / ((n + 1 : Nat) : Real) / (p ^ r * q ^ (n - r))) =
        (n : Real) * Real.log (n : Real) - (r : Real) * Real.log (r : Real) -
          (Nat.cast (n - r) : Real) * Real.log (Nat.cast (n - r) : Real) -
          Real.log ((n + 1 : Nat) : Real) := by
    rw [Real.log_div (by positivity) hprod.ne', Real.log_div (by norm_num) hn1.ne']
    simp only [Real.log_one, Real.log_inv]
    rw [Real.log_mul (pow_ne_zero r hp.ne') (pow_ne_zero (n - r) hq.ne'),
      Real.log_pow, Real.log_pow, Real.log_div hrR.ne' hn.ne',
      Real.log_div hsR.ne' hn.ne']

    push_cast
    linear_combination (Real.log (n : Real)) * hsumR
  rw [hlogid] at hlog
  calc
    Real.exp ((n : Real) * Real.log (n : Real) - (r : Real) * Real.log (r : Real) -
        (Nat.cast (n - r) : Real) * Real.log (Nat.cast (n - r) : Real) -
        Real.log ((n + 1 : Nat) : Real)) <= Real.exp (Real.log (Nat.choose n r : Real)) := by
      apply Real.exp_le_exp.mpr
      exact hlog
    _ = (Nat.choose n r : Real) := Real.exp_log hchoosepos