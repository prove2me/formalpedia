-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:53:08.785263+00:00
-- url     : https://prove2.me/submissions/f12a37fc-503c-405b-a26f-921c92e26a11

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

/-- Uniform continuity controls contact value differences even when the
base points change with the physical grid and do not converge. -/
theorem solution
    (w : ℝ → ℝ) (s : Set ℝ) (hw : UniformContinuousOn w s)
    (z c : ℕ → ℝ)
    (hz : ∀ m, z m ∈ s) (hzc : ∀ m, z m + c m ∈ s)
    (hc : Tendsto c atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => w (z m + c m) - w (z m))
      atTop (nhds (0 : ℝ)) := by
  apply (Metric.tendsto_atTop).2
  intro ε hε
  obtain ⟨δ, hδ, hUC⟩ := (Metric.uniformContinuousOn_iff.1 hw) ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).1 hc δ hδ
  refine ⟨N, ?_⟩
  intro m hm
  have hsmall : |c m| < δ := by
    simpa only [Real.dist_eq, sub_zero] using hN m hm
  have hdist : dist (z m) (z m + c m) < δ := by
    simpa [Real.dist_eq, abs_neg] using hsmall
  have hvalue := hUC (z m) (hz m) (z m + c m) (hzc m) hdist
  simpa [Real.dist_eq, sub_zero, abs_sub_comm] using hvalue
