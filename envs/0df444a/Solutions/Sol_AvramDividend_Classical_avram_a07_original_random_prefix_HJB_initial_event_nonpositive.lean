-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_original_random_prefix_HJB_initial_event_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:48:57.425271+00:00
-- url     : https://prove2.me/submissions/4b49ba76-75bb-40b4-86d4-54fe4b20c952

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a07_original_allvariation_random_stopped_prefix_HJB_nonpositive
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
      ENNReal.ofReal (riskProcess X x D (u i) ω) < C)
    (G : Ω → ℝ)
    (hG : ∀ ω, G ω =
      (∑ i ∈ Finset.range (k ω),
        Real.exp (-(q * (u i : ℝ))) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) *
            (X.generator w (riskProcess X x D (u i) ω) -
              q * w (riskProcess X x D (u i) ω)) +
          (D (u (i + 1)) ω - D (u i) ω) *
            (1 - deriv w (riskProcess X x D (u i) ω)))))
    (hGI : Integrable G P) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, G ω ∂P) ≤ 0 := by
  intro A hA
  apply integral_nonpos_of_ae
  filter_upwards [] with ω
  rw [hG ω]
  exact avram_a07_original_allvariation_random_stopped_prefix_HJB_nonpositive
    X q w C hw_gen hw_grad x D hD u hu k hregion ω