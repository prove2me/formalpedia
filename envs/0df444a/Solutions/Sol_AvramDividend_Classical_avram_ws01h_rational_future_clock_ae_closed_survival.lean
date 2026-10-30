-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_rational_future_clock_ae_closed_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:01:57.641753+00:00
-- url     : https://prove2.me/submissions/76bc1f4e-ca05-49e8-8544-6a390e8d4c19

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_open_survival_iff_weak_lower_clock
import Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_killed_closed_history_ae_time_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_ennreal_strict_clock_single_time_null_ws01a

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact rational pre-clock survival agrees with full closed-horizon
survival for almost every genuine real exponential observation age. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (ω : Ω) :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      (0 ≤ t ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal t →
          0 ≤ x + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω) ↔
      (0 ≤ t ∧ ∀ s : ℝ≥0, s ≤ Real.toNNReal t →
          0 ≤ x + X.X s ω) := by
  let τ : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  have hzero :
      (volume : Measure ℝ)
        {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t = τ} = 0 :=
    chat04_ennreal_strict_clock_single_time_null_ws01a τ
  have hne : ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      0 ≤ t → ENNReal.ofReal t ≠ τ := by
    apply (ae_iff).2
    simpa only [_root_.not_imp, not_not] using hzero
  have hclosed :=
    chat04_strict_lower_killed_closed_history_ae_time_ws01a
      X (-x) ω
  filter_upwards [hne, hclosed] with t ht hc
  constructor
  · rintro ⟨ht0, hgrid⟩
    have hweak : (Real.toNNReal t : ℝ≥0∞) ≤ τ := by
      simpa only [τ] using
        (avram_ws01h_rational_open_survival_iff_weak_lower_clock
          X x ω (Real.toNNReal t)).mp hgrid
    have hstrict : ENNReal.ofReal t < τ := by
      exact lt_of_le_of_ne hweak (ht ht0)
    have hfull := (hc.mp ⟨ht0, hstrict⟩).2
    refine ⟨ht0, ?_⟩
    intro s hs
    have h := hfull s hs
    linarith
  · rintro ⟨ht0, hfull⟩
    have hLower : ∀ s : ℝ≥0,
        s ≤ Real.toNNReal t → -x ≤ X.X s ω := by
      intro s hs
      have h := hfull s hs
      linarith
    have hstrict : ENNReal.ofReal t < τ :=
      (hc.mpr ⟨ht0, hLower⟩).2
    have hweak : (Real.toNNReal t : ℝ≥0∞) ≤
        twoSidedExitDownTime X (-x) ω := by
      change ENNReal.ofReal t ≤ τ
      exact hstrict.le
    refine ⟨ht0, ?_⟩
    exact
      (avram_ws01h_rational_open_survival_iff_weak_lower_clock
        X x ω (Real.toNNReal t)).mpr hweak
