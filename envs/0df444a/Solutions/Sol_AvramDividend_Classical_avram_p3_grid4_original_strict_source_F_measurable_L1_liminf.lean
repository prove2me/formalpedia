-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_strict_source_F_measurable_L1_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:40:45.618527+00:00
-- url     : https://prove2.me/submissions/12b08f84-7c8e-4a57-aeba-046c35c2904a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_constant_strict_Fatou_payoff_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Package the actual nonnegative strict payoff and its Fatou liminf. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    ∃ F : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n) ∧ Integrable (F n) P ∧ 0 ≤ᵐ[P] F n) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  obtain ⟨F, hMeas, hInt, hPos, hLiminf⟩ :=
    avram_p3_bv_original_constant_strict_Fatou_payoff_grid
      X hBV x C D hD w hw_cont hw_neg q hq T hT hTpos hw_nonneg
  exact ⟨F, (fun n => ⟨hMeas n, hInt n, hPos n⟩), hLiminf⟩
