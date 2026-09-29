-- Prove2me | solution 1 for Erdos77.binomial_entropy_log_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T19:58:52.050294+00:00
-- url     : https://prove2.me/submissions/4fe0761f-8f18-4d68-8251-48c904be1aa5

import Mathlib
import Theorems.Thm_Erdos77_binomial_entropy_integer_form
open Filter Topology

theorem solution (n r : Nat) (hr : 0 < r) (hrn : r < n) :
    Real.exp ((n : Real) * Real.log (n : Real) - (r : Real) * Real.log (r : Real) -
      (Nat.cast (n - r) : Real) * Real.log (Nat.cast (n - r) : Real) -
      Real.log ((n + 1 : Nat) : Real)) ≤ (Nat.choose n r : Real) := by
  have hpoly := Erdos77.binomial_entropy_integer_form n r hr hrn
  have hn : (0 : Real) < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hsR : (0 : Real) < (Nat.cast (n - r) : Real) := by
    exact_mod_cast (show 0 < n - r by omega)
  have hden : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hc : (0 : Real) < (Nat.choose n r : Real) := by
    exact_mod_cast Nat.choose_pos (le_of_lt hrn)
  have hbase : (0 : Real) < (n : Real) ^ n := by positivity
  have hlog := Real.log_le_log hbase hpoly
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have htarget :
      (n : Real) * Real.log (n : Real) - (r : Real) * Real.log (r : Real) -
        (Nat.cast (n - r) : Real) * Real.log (Nat.cast (n - r) : Real) -
        Real.log ((n + 1 : Nat) : Real) ≤ Real.log (Nat.choose n r : Real) := by
    push_cast
    nlinarith [hlog]
  rw [← Real.exp_log hc]
  exact Real.exp_le_exp.mpr htarget
