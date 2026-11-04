-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_lebesgue_zero_cap_contact_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:16:03.32227+00:00
-- url     : https://prove2.me/submissions/84e8e331-4755-43e2-bd75-877c7844f1cc

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_fulltime_boundary_weight_zero_of_ae_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A UBV controlled reserve spends zero atomless physical-generator time at zero or finite cap before a ruin-dominated clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D s ω ≤ c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] (hZeroMass : μ {0} = 0)
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if (t : ℝ≥0∞) < τ ω ∧
          (riskProcess X x D t ω = 0 ∨
           riskProcess X x D t ω = c)
        then weight t ω else 0 ∂μ) = 0 := by
  have hZero : ∀ᵐ t : ℝ≥0 ∂μ, t ≠ 0 :=
    by
      rw [ae_iff]
      simpa using hZeroMass
  exact avram_p4_e_localise_original_ruin_stopped_fulltime_boundary_weight_zero_of_ae_positive
    X hBV x c D hD hDiv hCap τ hτ
    μ hZero weight