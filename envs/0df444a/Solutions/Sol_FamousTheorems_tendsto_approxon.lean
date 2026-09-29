-- Prove2me | solution 1 for FamousTheorems.tendsto_approxon
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:08.715198+00:00
-- url     : https://prove2.me/submissions/92ea7aae-b919-4423-9e21-b686c9aa68ae

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] 
    [inst_1 : PseudoEMetricSpace α] [inst_2 : OpensMeasurableSpace α] [inst_3 : MeasurableSpace β] {f : β → α} 
    (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [inst_4 : TopologicalSpace.SeparableSpace ↑s] {x : β}, 
    f x ∈ closure s → Tendsto (fun n => (MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀ n) x) atTop (𝓝 (f x)) :=
  @_root_.MeasureTheory.SimpleFunc.tendsto_approxOn
