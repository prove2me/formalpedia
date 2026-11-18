-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_long_joint_tube_original_zero_noise_cash_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T22:22:04.212521+00:00
-- url     : https://prove2.me/submissions/9ee10b48-128e-4c28-92b4-e9e0359f2c8d

import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSourceLong : ∀ s : ℝ≥0, s ≤ (17 / 16000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCenteredLong : ∀ s : ℝ≥0, s ≤ (17 / 16000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (hTubeLong : ∀ s : ℝ≥0, s ≤ (17 / 16000 : ℝ≥0) →
      |X.X s ω| ≤ (1 / 400 : ℝ)) :
    ¬ (Real.exp (-(1 / 100000 : ℝ)) *
         (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
       (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
         (3 / 16 : ℝ) ≤ (1 / 1936 : ℝ) := by 
  have hShort : (1 / 1000 : ℝ≥0) ≤ (17 / 16000 : ℝ≥0) := by
    apply (NNReal.coe_le_coe).mp
    norm_num
  have hFinite :=
    avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
      X ω (1 / 1000) (1 / 100) (by norm_num)
  have hReject :=
    avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
      X ω B
      (fun s hs => hSourceLong s (hs.trans hShort))
      (fun s hs => hCenteredLong s (hs.trans hShort))
      (fun s hs => hTubeLong s (hs.trans hShort))
      hFinite (0 : ℝ) (by norm_num)
  simpa only [zero_add] using hReject
