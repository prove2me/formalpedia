-- Prove2me | solution 1 for BilateralProfitLB.claim_3_6
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T13:34:28.824191+00:00
-- url     : https://prove2.me/submissions/e2ae6e86-fad1-47f2-95c3-5d75c9e7b244

import Theorems.Thm_BilateralProfitLB_expCount_transfer_randomized

open MeasureTheory BilateralProfitLB

theorem solution (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) (T : ℕ)
    (π : Policy Unit) :
    expCount π (Measure.dirac ()) (law K j) T (I K j) -
        expCount π (Measure.dirac ()) (law K 0) T (I K j) ≤
      (T : ℝ) / (22 * (K : ℝ) ^ 2) *
        Real.sqrt (expCount π (Measure.dirac ()) (law K 0) T (I K j)) :=
  expCount_transfer_randomized K hK j hj1 hjK T Unit (Measure.dirac ()) π
