-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_generator_uniform_cell_active_set_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:53:53.350466+00:00
-- url     : https://prove2.me/submissions/7fea12d4-df15-4f60-9539-9fbc45b106b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original pre-payment reserve and ruin clock define a measurable interior cell. -/
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
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n i, i < n + 1 → MeasurableSet {ω : Ω |
      let Z : ℕ → ℝ := fun j => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
      (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C} := by
  intro n i hii
  let Z : Ω → ℝ := fun ω => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  have hZ : Measurable Z := by
    have hpair : Measurable (fun ω : Ω => ((u n i, ω) : ℝ≥0 × Ω)) :=
      measurable_const.prodMk measurable_id
    exact (avram_integration_sweep9_original_controlled_prestate_ambient_measurable
      X x D hD.1.1).comp hpair
  have hruin : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD.1.1
  have h₁ : MeasurableSet {ω : Ω | (u n i : ℝ≥0∞) < ruinTime X x D ω} :=
    measurableSet_lt measurable_const hruin
  have h₂ : MeasurableSet {ω : Ω | 0 < Z ω} :=
    measurableSet_lt measurable_const hZ
  have h₃ : MeasurableSet {ω : Ω | ENNReal.ofReal (Z ω) < C} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp hZ) measurable_const
  change MeasurableSet {ω : Ω |
    (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z ω ∧ ENNReal.ofReal (Z ω) < C}
  exact h₁.inter (h₂.inter h₃)
