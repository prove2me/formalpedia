-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_single_signed_strict_source_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:25:06.099688+00:00
-- url     : https://prove2.me/submissions/d58b0e85-a1b3-49a7-b82a-03e2bee45b38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Reduce the single original signed strict-source witness to the genuine
    cofinal-grid expected budget, retaining the actual original dividend cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ Z : Ω → ℝ,
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤ w x + Z ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let S : ℝ≥0 := ⟨T, hT⟩
  let Strict : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
     else 0)
  have hL1 : Integrable Strict P := by
    simpa [Strict, S] using
      (avram_p3_bv_original_prebudget_L1
        X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT)
  obtain ⟨u, huMono, huNonneg, huLT, huCofinal, huBudget⟩ :=
    avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  have huBound : ∀ n, u n ≤ (S : ℝ) := by
    intro n
    exact le_of_lt (huLT n)
  have hSReal : (S : ℝ) = T := rfl
  have hMean : (∫ ω, Strict ω ∂P) ≤ w x := by
    simpa only [hSReal] using
      (avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
        X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
        S u huMono huNonneg huBound huCofinal (w x) huBudget)
  refine ⟨fun ω => Strict ω - w x, hL1.sub (integrable_const _), ?_, ?_⟩
  · have hSubtract :
        (∫ ω, Strict ω - w x ∂P) =
          (∫ ω, Strict ω ∂P) - w x := by
      simp [integral_sub hL1 (integrable_const (w x))]
    rw [hSubtract]
    exact sub_nonpos.mpr hMean
  · filter_upwards [] with ω
    dsimp [Strict, S]
    linarith
