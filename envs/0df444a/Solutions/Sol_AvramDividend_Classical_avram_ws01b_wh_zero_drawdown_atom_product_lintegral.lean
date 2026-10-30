-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_wh_zero_drawdown_atom_product_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:27:36.189227+00:00
-- url     : https://prove2.me/submissions/d750783c-0675-48e2-bcc2-72e0fa3674f8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- An independent terminal drawdown zero atom factors from the
nonnegative upper-supremum reward. Useful at BV reserve zero. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (g : α → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ a : α × ℝ,
      if a.2 = 0 then g a.1 else 0 ∂(μ.prod ν)) =
    ν ({0} : Set ℝ) * (∫⁻ a, g a ∂μ) := by
  classical
  have hf : Measurable (fun a : α × ℝ =>
      if a.2 = 0 then g a.1 else (0 : ℝ≥0∞)) :=
    Measurable.ite
      ((measurableSet_singleton (0 : ℝ)).preimage measurable_snd)
      (hg.comp measurable_fst) measurable_const
  rw [lintegral_prod _ hf.aemeasurable]
  calc
    _ = ∫⁻ x : α, ν ({0} : Set ℝ) * g x ∂μ := by
      congr 1
      funext x
      have hI := lintegral_indicator
        (measurableSet_singleton (0 : ℝ))
        (fun _ : ℝ => g x) (μ := ν)
      simpa [Set.indicator, Set.mem_singleton_iff, mul_comm] using hI
    _ = ν ({0} : Set ℝ) * (∫⁻ x, g x ∂μ) :=
      lintegral_const_mul _ hg
