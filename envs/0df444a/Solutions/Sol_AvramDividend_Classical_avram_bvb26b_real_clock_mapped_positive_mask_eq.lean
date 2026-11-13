-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb26b_real_clock_mapped_positive_mask_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:38:00.90652+00:00
-- url     : https://prove2.me/submissions/1b62be7e-7da2-4307-92e6-82fcdc19d842

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem solution
    (T a : ℝ) (f : ℝ≥0 → ℝ) (p : ℝ≥0 → Prop)
    [DecidablePred p] :
    (∫ r in Set.Icc (0 : ℝ) T,
      (if 0 < Real.toNNReal r ∧
          ((Real.toNNReal r : ℝ≥0) : ℝ) < a ∧ p (Real.toNNReal r)
       then f (Real.toNNReal r) else 0)) =
    (∫ r in Set.Icc (0 : ℝ) T,
      (if 0 < r ∧ r < a ∧ p (Real.toNNReal r)
       then f (Real.toNNReal r) else 0)) := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have hr0 : 0 ≤ r := hr.1
  have hcoe : ((Real.toNNReal r : ℝ≥0) : ℝ) = r :=
    Real.coe_toNNReal _ hr0
  simp only [hcoe, Real.toNNReal_pos]
