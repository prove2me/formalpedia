-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_reward_measurable_version
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:48:43.348577+00:00
-- url     : https://prove2.me/submissions/6f031e34-b696-451a-92e5-ff3bf78a91f3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The exact original strict BV reward has a measurable nonnegative L1
representative. This removes an artificial pointwise-measurability
requirement from its eventual finite-grid Fatou implementation. -/
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
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    ∃ F : Ω → ℝ,
      Measurable F ∧ Integrable F P ∧
      (0 ≤ᵐ[P] F) ∧ (F =ᵐ[P] Strict) := by
  intro S Strict
  obtain ⟨hInt, hPos⟩ :=
    avram_p3_bv_original_strict_reward_L1_nonnegative
      X hBV x C D hD w hw_cont hw_neg q hq T hT hTpos hw_nonneg
  have hAE : AEMeasurable Strict P := hInt.aemeasurable
  let F : Ω → ℝ := hAE.mk Strict
  refine ⟨F, hAE.measurable_mk, ?_, ?_, hAE.ae_eq_mk.symm⟩
  · exact hInt.congr hAE.ae_eq_mk
  · filter_upwards [hAE.ae_eq_mk] with ω hEq
    change 0 ≤ hAE.mk Strict ω
    rw [← hEq]
    exact hPos ω
