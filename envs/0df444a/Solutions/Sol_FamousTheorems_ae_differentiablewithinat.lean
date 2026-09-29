-- Prove2me | solution 1 for FamousTheorems.ae_differentiablewithinat
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:12.282888+00:00
-- url     : https://prove2.me/submissions/33a42915-e55d-4b6c-ac16-b57e7bf399b2

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
    [inst_2 : MeasurableSpace E] [BorelSpace E] {F : Type u_2} [inst_4 : NormedAddCommGroup F] [inst_5 : NormedSpace ℝ F] 
    {C : NNReal} {s : Set E} {μ : MeasureTheory.Measure E} [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] 
    [μ.IsAddHaarMeasure] {f : E → F}, 
    LipschitzOnWith C f s → MeasurableSet s → ∀ᵐ (x : E) ∂μ.restrict s, DifferentiableWithinAt ℝ f s x :=
  @_root_.LipschitzOnWith.ae_differentiableWithinAt
