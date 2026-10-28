-- Prove2me | solution 1 for AvramDividend.Classical.bv_nonnegative_tails_bundle_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:57:24.498167+00:00
-- url     : https://prove2.me/submissions/bc69885d-87d6-4b36-a1cb-c486b500a4b6

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ)
    (hNonneg : ∀ n ω, 0 ≤ f n ω)
    (hTail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | ε ≤ f n ω}) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => (0 : ℝ)) := by
  apply (tendstoInMeasure_iff_measureReal_dist).2
  intro ε hε
  have hSet (n : ℕ) :
      {ω | ε ≤ dist (f n ω) (0 : ℝ)} =
        {ω | ε ≤ f n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg (hNonneg n ω)]
  simpa only [hSet] using hTail ε hε
