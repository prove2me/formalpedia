-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_shifted_lower_closed_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:51:11.510349+00:00
-- url     : https://prove2.me/submissions/b11c8549-1f9c-4b24-9ff6-bc6de783c586

import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Measurability of the true continuously monitored lower-killed
future window, with original path and arbitrary initial capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s T : ℝ≥0) :
    MeasurableSet {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)} := by
  have hsT : s ≤ s + T :=
    le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ T)
  have hbase := chat04_lower_survival_closed_window_measurable
    X (-x) s (s + T) hsT
  have hEq :
      {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
        0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)} =
      {ω : Ω | ∀ w : ℝ≥0, s ≤ w → w ≤ s + T →
        ¬ X.X w ω < -x} := by
    ext ω
    constructor
    · intro h w hsw hwu
      have hsub : w - s ≤ T := by
        have hu := tsub_le_tsub_right hwu s
        simpa using hu
      have h0 := h (w - s) hsub
      have heq : s + (w - s) = w := add_tsub_cancel_of_le hsw
      rw [heq] at h0
      have hx : 0 ≤ x + X.X w ω := by linarith
      linarith
    · intro h v hv
      have hs : s ≤ s + v :=
        le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ v)
      have hu : s + v ≤ s + T := by
        simpa only [add_comm] using (add_le_add_left hv s)
      have h0 := h (s + v) hs hu
      have hx : -x ≤ X.X (s + v) ω := le_of_not_gt h0
      linarith
  rw [hEq]
  exact hbase
