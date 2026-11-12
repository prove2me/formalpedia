-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_integrable_square_add_of_L2_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:06:12.212512+00:00
-- url     : https://prove2.me/submissions/b4112f81-76a5-4510-a8d1-688b22cf58dd

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (G J : α → ℝ)
    (hGm : AEStronglyMeasurable G μ)
    (hJm : AEStronglyMeasurable J μ)
    (hG : Integrable (fun ω => (G ω) ^ 2) μ)
    (hJ : Integrable (fun ω => (J ω) ^ 2) μ) :
    Integrable (fun ω => (G ω + J ω) ^ 2) μ := by
  have hg : MemLp G 2 μ :=
    (memLp_two_iff_integrable_sq hGm).2 hG
  have hj : MemLp J 2 μ :=
    (memLp_two_iff_integrable_sq hJm).2 hJ
  exact (memLp_two_iff_integrable_sq (hGm.add hJm)).1 (hg.add hj)
