-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose16_original_countable_stopping_strict_postpayment_preruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:25:45.451434+00:00
-- url     : https://prove2.me/submissions/673225c0-da1b-4241-b40f-bb181179819b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single almost-sure event supports strict original postpayment solvency at
all countably many genuine right-continuous stopping clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ j (s : ℝ≥0),
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ j ω ≤ s})
    (hstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ j ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ j,
      (τ j ω : ℝ≥0∞) < ruinTime X x D ω →
        0 < x + X.X (τ j ω) ω - rightLimit D (τ j ω) ω := by
  rw [ae_all_iff]
  intro j
  exact avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
    X hBV x C D hD (τ j) (hτ j) (hstop j)
