-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_countable_stopped_boundary_density_zero_common_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:17:42.30548+00:00
-- url     : https://prove2.me/submissions/daf0d4a4-886c-462f-8cc3-27a9c0332f05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- One conull event works for all countably many source localisers and time clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτ : ∀ k ω, τ k ω ≤ ruinTime X x D ω)
    (μ : ℕ → Measure ℝ≥0) (hμ : ∀ k, SFinite (μ k))
    (weight : ℕ → ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, ∀ k,
      (∫⁻ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ k ω ∧
        (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
        then weight k t ω else 0 ∂(μ k)) = 0 := by
  apply ae_all_iff.mpr
  intro k
  letI : SFinite (μ k) := hμ k
  exact avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
    X hBV x c D hD hDiv hCap (τ k) (hτ k) (μ k) (weight k)