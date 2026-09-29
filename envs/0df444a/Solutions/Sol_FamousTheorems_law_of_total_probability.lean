-- Prove2me | solution 1 for FamousTheorems.law_of_total_probability
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:06:46.83948+00:00
-- url     : https://prove2.me/submissions/f3045910-264e-4ff5-b15b-554eff282779

import Mathlib

open MeasureTheory

theorem solution {Ω α : Type*} {m : MeasurableSpace Ω} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x : α, μ (X ⁻¹' {x}) • ProbabilityTheory.cond μ (X ⁻¹' {x}) = μ :=
  ProbabilityTheory.sum_meas_smul_cond_fiber hX μ
