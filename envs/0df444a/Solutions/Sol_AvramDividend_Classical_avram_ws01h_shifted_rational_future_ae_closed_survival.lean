-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_shifted_rational_future_ae_closed_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:34:05.768095+00:00
-- url     : https://prove2.me/submissions/69306bc6-f7c7-419b-b755-149734a5984a

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_shifted_rational_survival_iff_weak_downclock
import Theorems.Thm_AvramDividend_Classical_chat04_ennreal_strict_clock_single_time_null_ws01a

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact rational-open-age reward is the genuine closed nonruin
survival reward at almost every residual real exponential clock age,
for every shifted original Lévy sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (ω : Ω) (b : ℝ≥0) :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      (0 ≤ t ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal t →
          0 ≤ x + (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω)) ↔
      (0 ≤ t ∧ ∀ s : ℝ≥0, s ≤ Real.toNNReal t →
        0 ≤ x + (X.X (b + s) ω - X.X b ω)) := by
  let D : ℝ≥0∞ :=
    ⨅ (s : ℝ≥0)
      (_ : x + (X.X (b + s) ω - X.X b ω) < 0), (s : ℝ≥0∞)
  have hnull :
      (volume : Measure ℝ)
        {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t = D} = 0 :=
    chat04_ennreal_strict_clock_single_time_null_ws01a D
  have hne : ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      0 ≤ t → ENNReal.ofReal t ≠ D := by
    apply (ae_iff).2
    simpa only [_root_.not_imp, not_not] using hnull
  filter_upwards [hne] with t ht
  constructor
  · rintro ⟨ht0, hgrid⟩
    have hweak : (Real.toNNReal t : ℝ≥0∞) ≤ D := by
      simpa only [D] using
        (avram_ws01h_shifted_rational_survival_iff_weak_downclock
          X x ω b (Real.toNNReal t)).mp hgrid
    have hstrict : ENNReal.ofReal t < D :=
      lt_of_le_of_ne hweak (ht ht0)
    refine ⟨ht0, ?_⟩
    intro s hs
    by_contra hn
    have hCross : x + (X.X (b + s) ω - X.X b ω) < 0 :=
      lt_of_not_ge hn
    have hDownLe : D ≤ (s : ℝ≥0∞) := by
      exact iInf_le_of_le s (iInf_le_of_le hCross le_rfl)
    have hBad : (Real.toNNReal t : ℝ≥0∞) <
        (Real.toNNReal t : ℝ≥0∞) :=
      (hstrict.trans_le hDownLe).trans_le
        (ENNReal.coe_le_coe.mpr hs)
    exact (lt_irrefl _ hBad)
  · rintro ⟨ht0, hclosed⟩
    refine ⟨ht0, ?_⟩
    intro n hn k hk
    exact hclosed _ hk.le
