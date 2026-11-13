-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb43_original_strict_physical_prefix_discounted_cash_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:52:14.785716+00:00
-- url     : https://prove2.me/submissions/1e5a077d-be40-4940-ba3d-561f0ef9c4bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (q : ℝ) (σ : ℝ≥0∞)
    (μ : Measure ℝ) (n k : ℕ) (hnk : n ≤ k) :
    (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((n : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
    (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((k : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by
  have hCast : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
  have hk : 0 < (k : ℝ) + 2 := by positivity
  have hn : 0 < (n : ℝ) + 2 := by positivity
  have hden : ((n : ℝ) + 2) ≤ ((k : ℝ) + 2) := by linarith
  have hFrac : T / ((k : ℝ) + 2) ≤ T / ((n : ℝ) + 2) := by
    apply (div_le_div_iff₀ hk hn).2
    nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hden)]
  have hCut : T - T / ((n : ℝ) + 2) ≤ T - T / ((k : ℝ) + 2) := by
    linarith only [hFrac]
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  exact ⟨ht.1, lt_of_lt_of_le ht.2 hCut⟩
