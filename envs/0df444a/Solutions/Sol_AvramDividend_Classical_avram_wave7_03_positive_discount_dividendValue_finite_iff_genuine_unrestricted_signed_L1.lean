-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_positive_discount_dividendValue_finite_iff_genuine_unrestricted_signed_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:44:53.364316+00:00
-- url     : https://prove2.me/submissions/fadc36f3-f359-47b9-9104-7e53e6fb02d6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_perpetual_value_finite_iff_cash_toReal_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Positive-discount canonical expected original ENNReal cash is finite iff
    the unrestricted actual signed real Stieltjes payout is L1(P). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    (dividendValue X q x D < ⊤) ↔
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hAeFin : ∀ᵐ ω ∂P, F ω < ⊤ :=
    avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
      X x C D hD q hq
  have hEq : (fun ω => (F ω).toReal) =ᵐ[P] g := by
    filter_upwards [hAeFin] with ω hω
    have hPath :=
      avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
        X x D hD.1.1 ω q hω
    have hgNN : 0 ≤ g ω := by
      apply integral_nonneg
      intro t
      exact (Real.exp_pos (-(q * t))).le
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal hPath.2.symm
      _ = g ω := ENNReal.toReal_ofReal hgNN
  constructor
  · intro hFinite
    have hFInt :=
      (avram_wave7_03_positive_discount_perpetual_value_finite_iff_cash_toReal_L1
        X x C D hD q hq).1 hFinite
    exact hFInt.congr hEq
  · intro hInt
    have hFInt : Integrable (fun ω => (F ω).toReal) P :=
      hInt.congr hEq.symm
    exact (avram_wave7_03_positive_discount_perpetual_value_finite_iff_cash_toReal_L1
      X x C D hD q hq).2 hFInt
