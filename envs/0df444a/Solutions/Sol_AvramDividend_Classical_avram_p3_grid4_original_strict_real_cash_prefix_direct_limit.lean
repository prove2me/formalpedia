-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:19:40.203443+00:00
-- url     : https://prove2.me/submissions/c7e6a07b-ae19-43d6-abd1-8bd2a2b6ac91

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_horizon_cash_prefix_tendsto_full
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite original strict-horizon cash converts the monotone ENNReal limit to real cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by
  have hENN :=
    avram_p3_grid4_original_strict_horizon_cash_prefix_tendsto_full
      X x C D hD ω q hq T hT δ hδpos hδanti hδ
  have hfin :=
    avram_limit2_original_strict_discounted_cash_finite_all_paths
      X q hq x D hD.1.1 ω T (le_of_lt hT)
  have hCont := ENNReal.continuousAt_toReal hfin
  have hReal := hCont.tendsto.comp hENN
  change Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal))
    at hReal
  exact hReal
