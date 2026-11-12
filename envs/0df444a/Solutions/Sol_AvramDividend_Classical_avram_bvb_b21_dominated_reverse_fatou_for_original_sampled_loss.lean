-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_dominated_reverse_fatou_for_original_sampled_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:41:39.983802+00:00
-- url     : https://prove2.me/submissions/5bac31a5-177e-48ad-a590-98817dbb3996

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- One-sided reverse Fatou for dominated nonnegative sampled losses. -/
theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ≥0∞) (g h : α → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hbound : ∀ n, f n ≤ᵐ[μ] g)
    (hfinite : (∫⁻ t, g t ∂μ) ≠ ⊤)
    (hpoint : ∀ᵐ t ∂μ,
      Filter.limsup (fun n : ℕ => f n t) Filter.atTop ≤ h t) :
    Filter.limsup (fun n : ℕ => ∫⁻ t, f n t ∂μ) Filter.atTop ≤
      ∫⁻ t, h t ∂μ := by
  calc
    _ ≤ ∫⁻ t, Filter.limsup (fun n : ℕ => f n t) Filter.atTop ∂μ :=
      MeasureTheory.limsup_lintegral_le g hf hbound hfinite
    _ ≤ ∫⁻ t, h t ∂μ := MeasureTheory.lintegral_mono_ae hpoint
