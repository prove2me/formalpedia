-- Prove2me | solution 1 for FamousTheorems.chebyshev_sum_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:17:47.724485+00:00
-- url     : https://prove2.me/submissions/fda24c77-3787-4970-ac48-948f3655676c

import Mathlib

theorem solution {ι : Type*} (s : Finset ι) {f g : ι → ℝ} (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) * ∑ i ∈ s, g i ≤ (s.card : ℝ) * ∑ i ∈ s, f i * g i :=
  hfg.sum_mul_sum_le_card_mul_sum
