-- Prove2me | solution 1 for Erdos77.uniform_binomial_entropy_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T14:18:51.303101+00:00
-- url     : https://prove2.me/submissions/8bf77f00-aa3b-4e45-934a-a789ccd0ff93

import Theorems.Thm_Erdos77_uniform_binomial_entropy_log_lower_bound
import Theorems.Thm_Erdos77_log_nat_linear_isLittleO
import Definitions.Def_Erdos77_asymmetric_ramsey
import Mathlib
open Filter Topology

theorem solution :
    Exists fun xi : Nat -> Real =>
      xi =o[atTop] (fun k : Nat => (k : Real)) /\
      forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
        Real.exp ((((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
          ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) - xi k) <=
          (Nat.choose (k + ell) ell : Real) := by
  refine ⟨fun k => Real.log (2 * (k : Real) + 1),
    Erdos77.log_nat_linear_isLittleO, ?_⟩
  intro k ell hk hell hle
  exact Erdos77.uniform_binomial_entropy_log_lower_bound k ell hk hell hle
