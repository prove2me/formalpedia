-- Prove2me | solution 1 for FamousTheorems.meas_ge_le_variance_div_sq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:33.884279+00:00
-- url     : https://prove2.me/submissions/fb096f51-b06f-4605-bdcc-517c38cd5854

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} 
    [MeasureTheory.IsFiniteMeasure μ] {X : Ω → ℝ}, 
    MeasureTheory.MemLp X 2 μ → 
    ∀ {c : ℝ}, 0 < c → μ {ω | c ≤ |X ω - ∫ (x : Ω), X x ∂μ|} ≤ ENNReal.ofReal (ProbabilityTheory.variance X μ / c ^ 2) :=
  @_root_.ProbabilityTheory.meas_ge_le_variance_div_sq
