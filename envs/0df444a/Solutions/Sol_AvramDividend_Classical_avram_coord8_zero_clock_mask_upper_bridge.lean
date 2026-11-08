-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord8_zero_clock_mask_upper_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:59:52.153215+00:00
-- url     : https://prove2.me/submissions/dbcf158f-254c-484a-b9d1-a2eb3052b29a

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

noncomputable section

/-- The source's zero-clock upper bound and an integrable positive-clock
masked reward yield the full expected upper bound by integral monotonicity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (b : ℝ) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFI : ∀ k, Integrable (F k) P)
    (hzero : ∀ k ω, σ k ω = 0 → F k ω ≤ b)
    (hpos : ∀ k,
      Integrable (fun ω => if σ k ω = 0 then b else F k ω) P ∧
      (∫ ω, if σ k ω = 0 then b else F k ω ∂P) ≤ b) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ b := by
  intro k
  have hpoint : ∀ ω, F k ω ≤
      (if σ k ω = 0 then b else F k ω) := by
    intro ω
    split_ifs with h
    · exact hzero k ω h
    · exact le_refl _
  have hmean := integral_mono_ae (hFI k) (hpos k).1
    (Filter.Eventually.of_forall hpoint)
  exact le_trans hmean (hpos k).2
