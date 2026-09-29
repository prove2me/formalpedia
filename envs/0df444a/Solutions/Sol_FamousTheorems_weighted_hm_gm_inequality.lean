-- Prove2me | solution 1 for FamousTheorems.weighted_hm_gm_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:57:33.134998+00:00
-- url     : https://prove2.me/submissions/68e6e00e-1587-4c31-8302-9078b3046908

import Mathlib

theorem solution {ι : Type*} (s : Finset ι) (w z : ι → ℝ) (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) : (∑ i ∈ s, w i / z i)⁻¹ ≤ ∏ i ∈ s, z i ^ w i :=
  Real.harm_mean_le_geom_mean_weighted s w z hs hw hw' hz
