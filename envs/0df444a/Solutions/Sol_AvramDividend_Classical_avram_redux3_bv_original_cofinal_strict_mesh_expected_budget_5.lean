-- Prove2me | solution 5 for AvramDividend.Classical.avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:53:03.790485+00:00
-- url     : https://prove2.me/submissions/f33750d7-607d-461b-b69b-67d792bfc1d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_physical_prefix_cofinal_clock
import Theorems.Thm_AvramDividend_Classical_avram_a19_all_cofinal_clocks_strict_source_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    let S : ℝ≥0 := ⟨T, hT⟩
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      (∀ n,
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ∂P) ≤ w x) := by
  classical
  let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  have hClock := avram_bv_strict6_original_physical_prefix_cofinal_clock T hTpos
  dsimp only at hClock
  have hMono : Monotone u := hClock.1
  have hNonneg : ∀ n, 0 ≤ u n := hClock.2.1
  have hCofinal : ∀ s : ℝ, s < T → ∃ n, s < u n := hClock.2.2.2
  have hStrict : ∀ n, u n < T := by
    intro n
    dsimp [u]
    have hdenom : 0 < (n : ℝ) + 2 := by positivity
    have hfrac : 0 < T / ((n : ℝ) + 2) := div_pos hTpos hdenom
    linarith
  refine ⟨u, hMono, hNonneg, hStrict, hCofinal, ?_⟩
  exact avram_a19_all_cofinal_clocks_strict_source_budget
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
    u hMono hNonneg hStrict hCofinal
