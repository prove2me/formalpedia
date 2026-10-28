-- Prove2me | solution 1 for AvramDividend.Classical.bv_grid_active_binomial_poisson_limit_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:56:13.21101+00:00
-- url     : https://prove2.me/submissions/3204b85f-7605-40f6-8a3d-b895dfa3e184

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_rare_grid_exponential_limit_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-- Exact Poisson mass limit for finite-activity grid cell indicators. -/
theorem solution
    (r : ℝ) (k : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((n.choose k : ℕ) : ℝ) *
          (1 - Real.exp (-(r / (n : ℝ)))) ^ k *
          Real.exp (-(r / (n : ℝ))) ^ (n - k))
      atTop
      (nhds (Real.exp (-r) * r ^ k / (k.factorial : ℝ))) := by
  have h := ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop
    (p := fun n : ℕ => 1 - Real.exp (-(r / (n : ℝ))))
    (r := r) k
    (AvramDividend.Classical.bv_rare_grid_exponential_limit_ws01b r)
  convert h using 1
  congr 1
  funext n
  ring
