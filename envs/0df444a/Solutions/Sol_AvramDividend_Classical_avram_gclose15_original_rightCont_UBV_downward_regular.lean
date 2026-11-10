-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose15_original_rightCont_UBV_downward_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:09:39.44156+00:00
-- url     : https://prove2.me/submissions/ed7eed82-60b9-4020-9b97-e5eb7ed1912b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Transport the original Levy downward regularity through its same-path right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by
  obtain ⟨Y, hYX, hYc, hYσ, hYν⟩ := levy_rightCont_process X
  have hYBV : ¬ Y.BoundedVariation := by
    intro h
    apply hBV
    simpa [SpectrallyNegativeLevy.BoundedVariation, hYσ, hYν] using h
  simpa only [hYX] using
    (avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid
      Y hYBV τ hτ hstop)
