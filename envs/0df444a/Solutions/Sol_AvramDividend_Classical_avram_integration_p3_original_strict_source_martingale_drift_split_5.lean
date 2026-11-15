-- Prove2me | solution 5 for AvramDividend.Classical.avram_integration_p3_original_strict_source_martingale_drift_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:02:35.981811+00:00
-- url     : https://prove2.me/submissions/9394026b-1057-4707-b448-cf853413a71a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_bv_topcap_original_full_T_strict_cash_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_a19_finite_cap_original_full_T_HJB_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- Source-faithful signed decomposition from the original full-horizon
   expectation, independently handled for C=top and finite C. This
   decomposition makes no assertion of a physical martingale identity. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ M B : Ω → ℝ,
      (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
      (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤ w x + M ω + B ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let S : ℝ≥0 := ⟨T, hT⟩
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
  have hYPair :=
    avram_p3_bv_original_strict_reward_L1_nonnegative
      X hBV x C D hD w hw_cont hw_neg q hq.le T hT hTpos hw_nonneg
  have hYI : Integrable Y P := hYPair.1
  have hMean : (∫ ω, Y ω ∂P) ≤ w x := by
    by_cases hTop : C = ⊤
    · simpa only [Y, S] using
        (avram_bv_topcap_original_full_T_strict_cash_expected_budget
          X hX hBV q hq w C hC hw_cont hw0 hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
          hjump T hT hTpos hTop)
    · simpa only [Y, S] using
        (avram_a19_finite_cap_original_full_T_HJB_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
          hjump T hT hTpos hTop)
  let B : Ω → ℝ := fun ω => Y ω - w x
  have hBI : Integrable B P := hYI.sub (integrable_const _)
  have hBmean : (∫ ω, B ω ∂P) ≤ 0 := by
    change (∫ ω, Y ω - w x ∂P) ≤ 0
    rw [integral_sub hYI (integrable_const _)]
    simpa using sub_nonpos.mpr hMean
  refine ⟨(fun _ => 0), B, ?_, ?_, ?_⟩
  · simp
  · exact ⟨hBI, hBmean⟩
  · filter_upwards [] with ω
    change Y ω ≤ w x + 0 + B ω
    dsimp [B]
    simp
