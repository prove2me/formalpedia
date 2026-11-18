-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB153_original_gaussian_tube_strict_stopped_cash_dominates_short_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:21:19.070999+00:00
-- url     : https://prove2.me/submissions/321ed449-f97e-46a4-ba16-807d0038fe44

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
import Theorems.Thm_AvramDividend_Classical_avram_gbB152_original_strict_prepayment_cash_contains_short_physical_cell
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original strict stopped Gaussian cash dominates interior Stieltjes cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S T : ℝ≥0) (hST : S < T)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ))
    (q : ℝ) :
    (∫⁻ t in Ioc (0 : ℝ) (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) ≤
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
      Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) := by
  have hSpre :=
    avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
      X T ω hTube S hST
  have hSub :=
    avram_gbB152_original_strict_prepayment_cash_contains_short_physical_cell
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)
      S T hSpre hST
  exact lintegral_mono_set hSub
