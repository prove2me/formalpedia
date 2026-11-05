-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:17:10.149688+00:00
-- url     : https://prove2.me/submissions/ad8cdeb4-ec4d-483f-a182-cbc23f92fcf1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strictly stopped source Stieltjes dividends converge in the L1 distance
defined by their original probability-space absolute error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n)
    (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    Tendsto (fun n => ∫ ω : Ω,
      |(∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal -
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal| ∂P)
      atTop (nhds 0) := by
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
  let G : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
  have hGI : Integrable G P :=
    avram_p3_bv_original_strict_cash_L1 X x C D hD q hq (S : ℝ) S.property
  have hFI (n : ℕ) : Integrable (F n) P :=
    avram_p3_bv_original_strict_cash_L1 X x C D hD q hq (u n) (hu n)
  have hUpper (n : ℕ) (ω : Ω) : F n ω ≤ G ω := by
    have hfin :
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ :=
      lt_of_le_of_lt
        (avram_p3_bv_original_strict_cash_rightlimit_bound
          D hD.1.1 ω (ruinTime X x D ω) S q hq)
        ENNReal.ofReal_lt_top
    exact ENNReal.toReal_mono (ne_of_lt hfin)
      (avram_p3_bv_original_cash_strict_horizon_mono
        X x q (u n) (S : ℝ) (hbelow n) D ω)
  have hEq (n : ℕ) :
      (∫ ω, |G ω - F n ω| ∂P) =
        (∫ ω, G ω ∂P) - (∫ ω, F n ω ∂P) := by
    have heq : (fun ω => |G ω - F n ω|) =
        (fun ω => G ω - F n ω) := by
      funext ω
      exact abs_of_nonneg (sub_nonneg.mpr (hUpper n ω))
    rw [heq]
    exact integral_sub hGI (hFI n)
  have hE := avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
    X x C D hD q hq S u hmono hu hbelow hcover
  change Tendsto (fun n => ∫ ω, F n ω ∂P)
    atTop (nhds (∫ ω, G ω ∂P)) at hE
  have hC : Tendsto (fun _ : ℕ => ∫ ω, G ω ∂P)
      atTop (nhds (∫ ω, G ω ∂P)) := tendsto_const_nhds
  have hlim : Tendsto
      (fun n => (∫ ω, G ω ∂P) - (∫ ω, F n ω ∂P))
      atTop (nhds 0) := by
    simpa only [sub_self] using hC.sub hE
  change Tendsto (fun n => ∫ ω, |G ω - F n ω| ∂P) atTop (nhds 0)
  convert hlim using 1
  funext n
  exact hEq n
