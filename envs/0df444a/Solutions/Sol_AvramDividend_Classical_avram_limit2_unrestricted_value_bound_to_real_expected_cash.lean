-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_unrestricted_value_bound_to_real_expected_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:52:01.036221+00:00
-- url     : https://prove2.me/submissions/90cb45ae-93e3-44a3-a964-a179b23e4758

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

/-- Any finite original unrestricted value bound gives every actual
    admissible strategy a genuine real L1 perpetual payout and mean bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ) (hw : 0 ≤ w)
    (hValueBound : valueFunction X q x ≤ ENNReal.ofReal w)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w := by
  have hValueLe : dividendValue X q x D ≤ valueFunction X q x := by
    unfold valueFunction
    exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  have hBound : dividendValue X q x D ≤ ENNReal.ofReal w :=
    hValueLe.trans hValueBound
  have hFinite : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt hBound ENNReal.ofReal_lt_top
  obtain ⟨hL1, hIdentity⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  refine ⟨hL1, hIdentity, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hw).mp
  simpa only [hIdentity] using hBound
