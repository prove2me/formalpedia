-- Prove2me | solution 1 for FamousTheorems.titu_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:10:03.769894+00:00
-- url     : https://prove2.me/submissions/d9a5b236-0c8e-43c9-b9fa-82f462ace871

import Mathlib

theorem solution {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i :=
  Finset.sq_sum_div_le_sum_sq_div s f hg
