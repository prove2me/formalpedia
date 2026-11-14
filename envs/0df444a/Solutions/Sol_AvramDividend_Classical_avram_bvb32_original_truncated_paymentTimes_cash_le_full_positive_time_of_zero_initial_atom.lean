-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb32_original_truncated_paymentTimes_cash_le_full_positive_time_of_zero_initial_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:28:54.618594+00:00
-- url     : https://prove2.me/submissions/1db7f229-8b40-4672-b79a-5f8119f5e8bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (σ : ℝ≥0∞) (μ : Measure ℝ)
    (hAtom : μ ({0} : Set ℝ) = 0)
    (b T : ℝ) (hbT : b ≤ T)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in paymentTimes σ ∩ Iio b, f t ∂μ) ≤
      (∫⁻ t in Ioc (0 : ℝ) T, f t ∂μ)  := by
  have hAE : ∀ᵐ t : ℝ ∂μ, t ≠ 0 := by
    simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using hAtom
  apply lintegral_mono_set'
  filter_upwards [hAE] with t ht
  intro hMem
  have hnon : 0 ≤ t := hMem.1.1
  have hlt : t < b := hMem.2
  have hpos : 0 < t := lt_of_le_of_ne hnon (Ne.symm ht)
  exact ⟨hpos, hlt.le.trans hbT⟩
