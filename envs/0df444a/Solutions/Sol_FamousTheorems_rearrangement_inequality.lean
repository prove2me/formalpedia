-- Prove2me | solution 1 for FamousTheorems.rearrangement_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:15:16.695468+00:00
-- url     : https://prove2.me/submissions/17b0d40a-0767-4af9-a1df-c6c6a541e2c5

import Mathlib

theorem solution {ι : Type*} [Fintype ι] {f g : ι → ℝ} (hfg : Monovary f g) (σ : Equiv.Perm ι) :
    ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i :=
  hfg.sum_mul_comp_perm_le_sum_mul
