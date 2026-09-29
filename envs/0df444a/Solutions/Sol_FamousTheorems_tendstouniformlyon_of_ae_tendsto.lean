-- Prove2me | solution 1 for FamousTheorems.tendstouniformlyon_of_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:13.525926+00:00
-- url     : https://prove2.me/submissions/4ea5d2eb-4775-4b2e-8ad7-2e2133e7d749

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} 
    [inst : PseudoEMetricSpace β] {μ : MeasureTheory.Measure α} [inst_1 : SemilatticeSup ι] [Nonempty ι] [Countable ι] 
    {f : ι → α → β} {g : α → β} {s : Set α}, 
    (∀ (n : ι), MeasureTheory.StronglyMeasurable (f n)) → 
    MeasureTheory.StronglyMeasurable g → 
    MeasurableSet s → 
    μ s ≠ ⊤ → 
    (∀ᵐ (x : α) ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) → 
    ∀ {ε : ℝ}, 0 < ε → ∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  @_root_.MeasureTheory.tendstoUniformlyOn_of_ae_tendsto
