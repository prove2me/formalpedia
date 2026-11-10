-- Prove2me | solution 10 for AvramDividend.Classical.avram_integration_p3_original_strict_source_residual_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:17:20.176374+00:00
-- url     : https://prove2.me/submissions/ab2d92f1-75aa-4b13-a0f2-eac587f63c1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_original_single_strict_clock_stopped_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_a19_positive_horizon_cofinal_simple_clocks
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A source-exact, acyclic direct bridge from the original physical
single-clock budget through strict cofinal cash to its integrable residual. -/
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
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤ w x + E ω) := by
  classical
  let S : ℝ≥0 := ⟨T, hT⟩
  obtain ⟨u, hu_mono, hu_nonneg, hu_lt, hu_cofinal⟩ :=
    avram_a19_positive_horizon_cofinal_simple_clocks T hTpos
  have hu_le : ∀ n, u n ≤ (S : ℝ) := by
    intro n
    change u n ≤ T
    exact le_of_lt (hu_lt n)
  have hprefix := fun n : ℕ =>
    (avram_a19_original_single_strict_clock_stopped_HJB_source
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos)
      (u n) (hu_nonneg n) (hu_lt n)
  have hMean :=
    avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      S u hu_mono hu_nonneg hu_le hu_cofinal (w x) hprefix
  exact avram_p3_bv_original_source_witness_from_strict_mean
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT hMean
