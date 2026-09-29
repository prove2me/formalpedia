-- Prove2me | solution 1 for FamousTheorems.continuous_of_dominated_interval
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:17.335871+00:00
-- url     : https://prove2.me/submissions/08cf6bbf-f4c3-4a71-8b0f-eedef2c31eb0

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℝ E] {μ : MeasureTheory.Measure ℝ} {X : Type u_2} [inst_2 : TopologicalSpace X] 
    [FirstCountableTopology X] {F : X → ℝ → E} {bound : ℝ → ℝ} {a b : ℝ}, 
    (∀ (x : X), MeasureTheory.AEStronglyMeasurable (F x) (μ.restrict (uIoc a b))) → 
    (∀ (x : X), ∀ᵐ (t : ℝ) ∂μ, t ∈ uIoc a b → ‖F x t‖ ≤ bound t) → 
    IntervalIntegrable bound μ a b → 
    (∀ᵐ (t : ℝ) ∂μ, t ∈ uIoc a b → Continuous fun x => F x t) → Continuous fun x => ∫ (t : ℝ) in a..b, F x t ∂μ :=
  @_root_.intervalIntegral.continuous_of_dominated_interval
