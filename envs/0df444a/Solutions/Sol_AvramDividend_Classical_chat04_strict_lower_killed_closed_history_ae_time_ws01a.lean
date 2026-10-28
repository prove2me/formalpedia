-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_lower_killed_closed_history_ae_time_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:10:44.477572+00:00
-- url     : https://prove2.me/submissions/6aef73d5-9ca6-43ac-b6ee-be8dd1465f61

import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_clock_weak_survival_past_ws01a
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A true lower-killing clock matches closed-history killing for a.e. time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ) (ω : Ω) :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      (0 ≤ t ∧ ENNReal.ofReal t < twoSidedExitDownTime X lower ω) ↔
      (0 ≤ t ∧ ∀ s : ℝ≥0, s ≤ Real.toNNReal t → lower ≤ X.X s ω) := by
  let τ : ℝ≥0∞ := twoSidedExitDownTime X lower ω
  have hsubset : {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t = τ} ⊆ {τ.toReal} := by
    rintro t ⟨ht, heq⟩
    change t = τ.toReal
    rw [← heq]
    exact (ENNReal.toReal_ofReal ht).symm
  have hzero :
      (volume : Measure ℝ) {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t = τ} = 0 :=
    Measure.mono_null hsubset (measure_singleton τ.toReal)
  have hne : ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      0 ≤ t → ENNReal.ofReal t ≠ τ := by
    apply (ae_iff).2
    simpa only [_root_.not_imp, not_not] using hzero
  refine hne.mono ?_
  intro t ht
  constructor
  · rintro ⟨ht0, hlt⟩
    refine ⟨ht0, ?_⟩
    intro s hs
    by_contra hn
    have hcross : X.X s ω < lower := lt_of_not_ge hn
    have hclock : τ ≤ (s : ℝ≥0∞) := by
      simpa only [τ, neg_neg] using
        (twoSidedExitDownTime_le_of_strict_lower_gap_observed
          X (-lower) ω s (by simpa only [neg_neg] using hcross))
    have hst : (s : ℝ≥0∞) ≤ ENNReal.ofReal t := by
      change (s : ℝ≥0∞) ≤ (Real.toNNReal t : ℝ≥0∞)
      exact ENNReal.coe_le_coe.mpr hs
    exact (not_lt_of_ge (le_trans hclock hst)) hlt
  · rintro ⟨ht0, hhistory⟩
    refine ⟨ht0, ?_⟩
    have hweak : (Real.toNNReal t : ℝ≥0∞) ≤ τ :=
      (chat04_lower_clock_weak_survival_past_ws01a
        X lower ω (Real.toNNReal t)).2
          (by intro s hs; exact hhistory s (le_of_lt hs))
    exact lt_of_le_of_ne hweak (ht ht0)
