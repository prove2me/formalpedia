-- Prove2me | solution 1 for FamousTheorems.integral_prod
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:17.322925+00:00
-- url     : https://prove2.me/submissions/4a5aadf5-151b-4b9c-9a79-63f9891dbc13

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
    [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} 
    [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν] [inst_4 : NormedSpace ℝ E] [MeasureTheory.SFinite μ] 
    (f : α × β → E), 
    MeasureTheory.Integrable f (μ.prod ν) → ∫ (z : α × β), f z ∂μ.prod ν = ∫ (x : α), ∫ (y : β), f (x, y) ∂ν ∂μ :=
  @_root_.MeasureTheory.integral_prod
