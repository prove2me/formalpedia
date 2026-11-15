-- Prove2me | solution 4 for AvramDividend.Classical.avram_integration_p3_original_strict_source_martingale_drift_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:19:42.119553+00:00
-- url     : https://prove2.me/submissions/9f2623c0-8be2-4f56-89b7-da898557feab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_top_cap_original_full_T_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_a19_finite_cap_original_full_T_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

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
  let F : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hF : Integrable F P :=
    (avram_p3_bv_original_strict_reward_L1_nonnegative X hBV x C D hD
      w hw_cont hw_neg q hq.le T hT hTpos hw_nonneg).1
  have hBudget : (∫ ω, F ω ∂P) ≤ w x := by
    by_cases hTop : C = ⊤
    · exact avram_a19_top_cap_original_full_T_HJB_source
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump T hT hTpos hTop
    · exact avram_a19_finite_cap_original_full_T_HJB_source
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump T hT hTpos hTop
  let a : ℝ := ∫ ω, F ω ∂P
  refine ⟨(fun ω => F ω - a), (fun _ => a - w x),
    ⟨hF.sub (integrable_const _), ?_⟩, ⟨integrable_const _, ?_⟩, ?_⟩
  · rw [integral_sub hF (integrable_const _)]
    simp [a]
  · simpa [a] using (sub_nonpos.mpr hBudget)
  · filter_upwards [] with ω
    change F ω ≤ w x + (F ω - a) + (a - w x)
    linarith
