-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_measurable_random_mark_interval_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:07:50.24188+00:00
-- url     : https://prove2.me/submissions/2e2f7a94-1a93-4f4c-8b74-b92c3ec11ac7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (a b : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (hY : ∀ j, Measurable (Y j)) :
    Measurable (fun ω => ∑ j ∈ Finset.Ico (a ω) (b ω), Y j ω) := by
  have hFamily : Measurable
      (fun ω : Ω => fun p : ℕ × ℕ =>
        ∑ j ∈ Finset.Ico p.1 p.2, Y j ω) := by
    apply measurable_pi_iff.mpr
    intro p
    exact Finset.measurable_sum (Finset.Ico p.1 p.2)
      (fun j _ => hY j)
  have hEval : Measurable
      (fun p : (ℕ × ℕ) × ((ℕ × ℕ) → ℝ) => p.2 p.1) := by
    exact measurable_from_prod_countable_right
      (fun p => measurable_pi_apply p)
  have hAB : Measurable (fun ω => (a ω, b ω)) := ha.prodMk hb
  simpa [Function.comp_def] using hEval.comp (hAB.prodMk hFamily)
