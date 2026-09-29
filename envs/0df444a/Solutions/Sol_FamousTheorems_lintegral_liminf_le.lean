-- Prove2me | solution 1 for FamousTheorems.lintegral_liminf_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:00.859693+00:00
-- url     : https://prove2.me/submissions/315b0ac2-db93-4810-949d-ba499536d333

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
    {ι : Type u_2} {f : ι → α → ENNReal} {u : Filter ι} [u.IsCountablyGenerated], 
    (∀ (i : ι), Measurable (f i)) → ∫⁻ (a : α), liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ (a : α), f i a ∂μ) u :=
  @_root_.MeasureTheory.lintegral_liminf_le
