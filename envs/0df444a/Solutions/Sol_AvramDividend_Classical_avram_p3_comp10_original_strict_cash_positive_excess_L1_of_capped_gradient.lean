-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp10_original_strict_cash_positive_excess_L1_of_capped_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:35:51.486633+00:00
-- url     : https://prove2.me/submissions/1024bf0e-b668-488f-bba5-b7dd5a2d3330

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp10_positivepart_L1_of_nonnegative_shift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact original strict stopped cash positive residual is L1,
using Avram's genuine capped derivative bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ n, Integrable (M n) P)
    (hBI : ∀ n, Integrable (B n) P) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∀ n, Integrable
      (fun ω => max (F n ω - (w x + (M n ω + B n ω))) 0) P := by
  dsimp only
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
  have hF : ∀ n, Integrable (F n) P :=
    avram_p3_comp8_original_canonical_strict_prefix_integrable
      X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg
  have hWx : 0 ≤ w x := le_trans hx
    (avram_limit2_bv_C1_closed_cap_payoff_above_reserve
      C hC w hw0 hw_cont hw_smooth hw_grad x hx hxc)
  intro n
  exact avram_p3_comp10_positivepart_L1_of_nonnegative_shift
    (F n) (fun ω => M n ω + B n ω)
    (hF n) ((hMI n).add (hBI n)) (w x) hWx
