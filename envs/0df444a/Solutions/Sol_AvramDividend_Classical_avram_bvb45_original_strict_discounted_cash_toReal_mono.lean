-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb45_original_strict_discounted_cash_toReal_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:59:27.331125+00:00
-- url     : https://prove2.me/submissions/83462485-8b9b-47fd-9649-feda19d275a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb43_original_strict_physical_prefix_discounted_cash_mono
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (q : ℝ) (σ : ℝ≥0∞)
    (μ : Measure ℝ)
    (hFinite : (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) < ⊤)
    (n k : ℕ) (hnk : n ≤ k) :
    (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((n : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal ≤
    (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((k : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal := by
  have hk : 0 ≤ T / ((k : ℝ) + 2) := by positivity
  have hCut : T - T / ((k : ℝ) + 2) ≤ T := sub_le_self _ hk
  have hSubset :
      paymentTimes σ ∩ Iio (T - T / ((k : ℝ) + 2)) ⊆
        paymentTimes σ ∩ Iic T := by
    intro t ht
    exact ⟨ht.1, le_trans (le_of_lt ht.2) hCut⟩
  have hBound :
      (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((k : ℝ) + 2)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
      (∫⁻ t in paymentTimes σ ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) :=
    MeasureTheory.lintegral_mono_set hSubset
  have hNotTop :
      (∫⁻ t in paymentTimes σ ∩ Iio (T - T / ((k : ℝ) + 2)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hBound hFinite)
  exact ENNReal.toReal_mono hNotTop
    (avram_bvb43_original_strict_physical_prefix_discounted_cash_mono
      T hT q σ μ n k hnk)
