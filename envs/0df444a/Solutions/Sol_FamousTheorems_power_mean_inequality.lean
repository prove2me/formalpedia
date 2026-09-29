-- Prove2me | solution 1 for FamousTheorems.power_mean_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:15:42.721532+00:00
-- url     : https://prove2.me/submissions/e37e3549-2c7e-482f-8080-978b9d702d9a

import Mathlib

theorem solution {ι : Type*} (s : Finset ι) (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) : (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p :=
  Real.rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp
