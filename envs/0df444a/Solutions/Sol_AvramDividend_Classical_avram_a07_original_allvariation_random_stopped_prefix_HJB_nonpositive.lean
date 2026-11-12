-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_original_allvariation_random_stopped_prefix_HJB_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:48:22.469507+00:00
-- url     : https://prove2.me/submissions/d45b6ece-bfb2-48fc-9856-7595670c2daf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a07_original_allvariation_admissible_grid_HJB_drift_nonpositive
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (k : Ω → ℕ)
    (hregion : ∀ ω i, i < k ω →
      0 < riskProcess X x D (u i) ω ∧
      ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    ∀ ω,
      (∑ i ∈ Finset.range (k ω),
        Real.exp (-(q * (u i : ℝ))) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) *
            (X.generator w (riskProcess X x D (u i) ω) -
              q * w (riskProcess X x D (u i) ω)) +
          (D (u (i + 1)) ω - D (u i) ω) *
            (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0 := by
  intro ω
  apply avram_a07_original_allvariation_admissible_grid_HJB_drift_nonpositive
    X q w C hw_gen hw_grad x D hD ω u hu
    (Finset.range (k ω))
  intro i hi
  exact hregion ω i (Finset.mem_range.mp hi)