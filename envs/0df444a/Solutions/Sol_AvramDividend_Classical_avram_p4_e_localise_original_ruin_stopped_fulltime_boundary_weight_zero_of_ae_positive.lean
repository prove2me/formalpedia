-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_fulltime_boundary_weight_zero_of_ae_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:35:30.163618+00:00
-- url     : https://prove2.me/submissions/fd27110a-04ff-4b27-a9f0-bee943844504

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Strict pre-ruin zero/cap occupation vanishes also at t=0 under an atomless initial physical clock. -/
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
    (μ : Measure ℝ≥0) [SFinite μ]
    (hμZero : ∀ᵐ t : ℝ≥0 ∂μ, t ≠ 0)
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0, if (t : ℝ≥0∞) < τ ω ∧
        (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
        then weight t ω else 0 ∂μ) = 0 := by
  have hPositive :=
    avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
      X hBV x c D hD hDiv hCap τ hτ μ weight
  filter_upwards [hPositive] with ω hω
  calc
    (∫⁻ t : ℝ≥0, if (t : ℝ≥0∞) < τ ω ∧
        (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
        then weight t ω else 0 ∂μ)
      = (∫⁻ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ ω ∧
        (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
        then weight t ω else 0 ∂μ) := by
          apply lintegral_congr_ae
          filter_upwards [hμZero] with t ht
          have hpos : 0 < t := pos_iff_ne_zero.mpr ht
          simp [hpos]
    _ = 0 := hω
