-- Prove2me | solution 1 for FamousTheorems.real_line_meagre_null_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:20:33.791556+00:00
-- url     : https://prove2.me/submissions/c97923c9-e1f7-462d-94c9-58daf3c910c5

import Mathlib

theorem solution : Disjoint (residual ℝ) (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
  Real.disjoint_residual_ae
