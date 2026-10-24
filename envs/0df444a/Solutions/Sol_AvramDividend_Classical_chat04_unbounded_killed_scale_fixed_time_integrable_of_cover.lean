-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_scale_fixed_time_integrable_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:55:38.632515+00:00
-- url     : https://prove2.me/submissions/adb4d534-6227-4ee1-9f85-88ea82237c03

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    Integrable
      (({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω))) P := by
  have hEquiv :
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} =
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → ¬ X.X s ω < -x} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h s hs hBad
      have hn := h s hs
      linarith
    · intro h s hs
      have hn := h s hs
      have hb : -x ≤ X.X s ω := le_of_not_gt hn
      linarith
  have hSurv : MeasurableSet[𝓕 t]
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} := by
    rw [hEquiv]
    exact chat03_lower_survival_filtration_measurable
      X τ hCover (-x) t
  have hSurvAmbient : MeasurableSet
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} :=
    (𝓕.le t) _ hSurv
  have hInt : Integrable (fun ω => W (x + X.X t ω)) P :=
    chat04_unbounded_scale_fixed_time_integrable X q hq W hW hnbv x t
  have hDisc : Integrable
      (fun ω => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t ω)) P := hInt.const_mul _
  exact hDisc.indicator hSurvAmbient
