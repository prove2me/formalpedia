-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_limit_preserves_nonpositive_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:10:22.798697+00:00
-- url     : https://prove2.me/submissions/0b751e32-ba6b-40c9-91f8-ba9fe8affe69

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original ruin-stopped nonpositive physical drift survives the a.s. clock limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P))
    (hNonpos : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ) ≤ 0) :
    ∀ᵐ ω ∂P, (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ) ≤ 0 := by
  have hLimit :=
    avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
      P X x C D hD μ f hf
  have hAll : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ) ≤ 0 := ae_all_iff.mpr hNonpos
  filter_upwards [hLimit, hAll] with ω hω hSign
  exact le_of_tendsto hω (Filter.Eventually.of_forall hSign)
