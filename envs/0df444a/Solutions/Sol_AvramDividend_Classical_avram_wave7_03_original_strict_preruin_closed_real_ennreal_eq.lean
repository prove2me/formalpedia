-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:08:18.079044+00:00
-- url     : https://prove2.me/submissions/a06acfb8-09fd-4535-bae6-59b33fdf7d41

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_finite_measure_payout_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact original pre-ruin cash equality at the same Stieltjes measure,
    including all continuous payment and right-limit atom mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (S : ℝ≥0)
    (hPre : S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in Icc (0 : ℝ) (S : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  have hSet :
      paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ) =
        Icc (0 : ℝ) (S : ℝ) := by
    exact avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
      X x D ω (fun _ => S) hPre
  have hFinite :
      (dividendMeasure D ω) (Icc (0 : ℝ) (S : ℝ)) ≠ ⊤ := by
    rw [avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω S]
    exact ne_of_lt ENNReal.ofReal_lt_top
  rw [hSet]
  exact discounted_stieltjes_finite_measure_payout_bridge
    q hq (dividendMeasure D ω) (Icc (0 : ℝ) (S : ℝ))
    measurableSet_Icc (fun t ht => ht.1) hFinite
