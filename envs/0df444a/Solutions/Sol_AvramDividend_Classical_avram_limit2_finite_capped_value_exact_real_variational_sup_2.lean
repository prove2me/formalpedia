-- Prove2me | solution 2 for AvramDividend.Classical.avram_limit2_finite_capped_value_exact_real_variational_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:56:31.482192+00:00
-- url     : https://prove2.me/submissions/f8780565-3c26-4f99-971c-b15456fa1520

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At finite genuine capped value, each original capped strategy has a
    real integrable payout, and the value is its exact real variational sup. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (C : ℝ≥0∞)
    (hFiniteCap : valueFunctionLe X q C x < ⊤) :
    (∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) ∧
    valueFunctionLe X q C x =
      ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissibleLe X x C D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hExact : ∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
      dividendValue X q x D =
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    intro D hD
    have hValueLe : dividendValue X q x D ≤ valueFunctionLe X q C x := by
      unfold valueFunctionLe
      exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
    have hFinite : dividendValue X q x D < ⊤ :=
      lt_of_le_of_lt hValueLe hFiniteCap
    exact avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1.1 q hFinite
  refine ⟨fun D hD => (hExact D hD).1, ?_⟩
  unfold valueFunctionLe
  refine iSup_congr fun D => iSup_congr fun hD => ?_
  exact (hExact D hD).2
