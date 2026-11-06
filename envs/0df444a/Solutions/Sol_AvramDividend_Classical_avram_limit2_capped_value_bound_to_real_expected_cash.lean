-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_capped_value_bound_to_real_expected_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:48:22.899024+00:00
-- url     : https://prove2.me/submissions/a0c3549f-3a70-4116-bc70-a4fc6e8842a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Any finite capped value upper bound yields real original perpetual
    Stieltjes L1 and a real expected-cash upper bound for each strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (C : ℝ≥0∞)
    (w : ℝ) (hw : 0 ≤ w)
    (hValueBound : valueFunctionLe X q C x ≤ ENNReal.ofReal w)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w := by
  have hValueLe : dividendValue X q x D ≤ valueFunctionLe X q C x := by
    unfold valueFunctionLe
    exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  have hBound : dividendValue X q x D ≤ ENNReal.ofReal w :=
    hValueLe.trans hValueBound
  have hFinite : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt hBound ENNReal.ofReal_lt_top
  obtain ⟨hL1, hIdentity⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1.1 q hFinite
  refine ⟨hL1, hIdentity, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hw).mp
  simpa only [hIdentity] using hBound
