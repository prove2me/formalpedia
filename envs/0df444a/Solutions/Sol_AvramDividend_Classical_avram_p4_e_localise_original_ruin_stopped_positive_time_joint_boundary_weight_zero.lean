-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:06:58.639119+00:00
-- url     : https://prove2.me/submissions/c80b045e-82d6-4c4c-97fb-ff0ca03b377c

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Every fixed physical-time clock ignores positive-time endpoint occupation.
    This does not claim random dividend Stieltjes or local-time mass vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ ω ∧
         (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
         then weight t ω else 0 ∂μ) = 0 := by
  have hZero :=
    avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
      X hBV x (ENNReal.ofReal c) D hD τ hτ μ
  have hUpper :=
    avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
      X hBV x c D hDiv μ hCap
  filter_upwards [hZero, hUpper] with ω hz hc
  have hWeight : ∀ᵐ t : ℝ≥0 ∂μ,
      (if 0 < t ∧ (t : ℝ≥0∞) < τ ω ∧
         (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
         then weight t ω else 0) = (0 : ℝ≥0∞) := by
    filter_upwards [hz, hc] with t hzt hct
    have hnot : ¬ (0 < t ∧ (t : ℝ≥0∞) < τ ω ∧
        (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)) := by
      intro h
      rcases h with ⟨ht0, hbefore, hboundary⟩
      have hpositive := hzt hbefore
      have hstrict := hct ⟨ht0, lt_of_lt_of_le hbefore (hτ ω)⟩
      rcases hboundary with h0 | hcap
      · exact (ne_of_gt hpositive) h0
      · exact (ne_of_lt hstrict) hcap
    simp only [if_neg hnot]
  simpa only [lintegral_zero] using (lintegral_congr_ae hWeight)