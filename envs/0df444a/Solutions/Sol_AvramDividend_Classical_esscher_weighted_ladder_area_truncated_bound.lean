-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_ladder_area_truncated_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:56:24.126306+00:00
-- url     : https://prove2.me/submissions/01518313-e3e3-4418-bbec-400387669375

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ladder_height_truncated_area_interval_bound
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_scalar_integrability_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Set
open AvramDividend.Classical

theorem solution
    (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    Real.exp (-(φ * z)) * (∫ t in (0 : ℝ)..z, min 1 t) ≤
      (1 + φ⁻¹) * min 1 (z ^ 2) := by
  calc
    Real.exp (-(φ * z)) * (∫ t in (0 : ℝ)..z, min 1 t) ≤
        Real.exp (-(φ * z)) * min (z ^ 2) z :=
      mul_le_mul_of_nonneg_left
        (ladder_height_truncated_area_interval_bound z hz)
        (Real.exp_pos _).le
    _ ≤ (1 + φ⁻¹) * min 1 (z ^ 2) :=
      esscher_tilted_tail_scalar_integrability_bound φ z hφ hz
