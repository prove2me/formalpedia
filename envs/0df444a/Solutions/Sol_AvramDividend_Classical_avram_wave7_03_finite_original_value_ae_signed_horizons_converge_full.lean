-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_value_ae_signed_horizons_converge_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:02:20.563161+00:00
-- url     : https://prove2.me/submissions/300acff5-2262-4360-82cf-cb3356dbb715

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_integrable_signed_horizon_tendsto_full_stieltjes_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A finite actual original dividend value yields almost-everywhere
    convergence of genuine signed horizons to full discounted Stieltjes cash. -/
/- Exact finite-value signed horizon convergence uses only a Proved source tail bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω))
        atTop (𝓝 (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω))) := by
  have hAeCash : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤ :=
    ((avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
      X x D hD q).mp hFinite).2
  filter_upwards [hAeCash] with ω hω
  exact
    avram_wave7_03_original_integrable_signed_horizon_tendsto_full_stieltjes_cash
      X x D ω q
      ((avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
        X x D hD ω q).mp hω)
