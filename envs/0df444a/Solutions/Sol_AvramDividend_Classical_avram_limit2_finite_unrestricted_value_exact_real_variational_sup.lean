-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_finite_unrestricted_value_exact_real_variational_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:56:22.916869+00:00
-- url     : https://prove2.me/submissions/7e4339a3-4b54-42f5-9f15-4b8bb5c556e5

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

/-- Finite original unrestricted value gives real L1 for every strategy and
    an exact variational supremum of genuine real ruin-stopped payout means. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (hFiniteValue : valueFunction X q x < ⊤) :
    (∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) ∧
    valueFunction X q x =
      ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissible X x D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hExact : ∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
      dividendValue X q x D =
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    intro D hD
    have hValueLe : dividendValue X q x D ≤ valueFunction X q x := by
      unfold valueFunction
      exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
    have hFinite : dividendValue X q x D < ⊤ :=
      lt_of_le_of_lt hValueLe hFiniteValue
    exact avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  refine ⟨fun D hD => (hExact D hD).1, ?_⟩
  unfold valueFunction
  refine iSup_congr fun D => iSup_congr fun hD => ?_
  exact (hExact D hD).2
