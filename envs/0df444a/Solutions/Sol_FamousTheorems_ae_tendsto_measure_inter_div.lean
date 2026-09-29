-- Prove2me | solution 1 for FamousTheorems.ae_tendsto_measure_inter_div
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:02:01.190761+00:00
-- url     : https://prove2.me/submissions/5203e46e-081d-42f6-8feb-64741496f263

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {β : Type u_1} [inst : MetricSpace β] [inst_1 : MeasurableSpace β] 
    [BorelSpace β] [SecondCountableTopology β] [HasBesicovitchCovering β] (μ : MeasureTheory.Measure β) 
    [MeasureTheory.IsLocallyFiniteMeasure μ] (s : Set β), 
    ∀ᵐ (x : β) ∂μ.restrict s, Tendsto (fun r => μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 1) :=
  @_root_.Besicovitch.ae_tendsto_measure_inter_div
