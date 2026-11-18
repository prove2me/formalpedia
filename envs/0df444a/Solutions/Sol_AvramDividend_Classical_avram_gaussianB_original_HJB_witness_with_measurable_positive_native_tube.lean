-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_HJB_witness_with_measurable_positive_native_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:51:06.975355+00:00
-- url     : https://prove2.me/submissions/7cfe07c3-1244-4f16-a3a1-23d90adac78c

import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_canonical_measurable_positive_joint_long_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Measurable positive canonical tube attached to a genuine admissible Gaussian source. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        ∀ ω ∈ E, ∀ s : unitInterval,
          s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
          |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
          |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω + 2 * (s : ℝ)| ≤
            (1 / 400 : ℝ) := by
  obtain ⟨𝓕, Y, hpath, hStand, hUBV, h0, hcont,
    hneg, hC2, hGen, hAdm⟩ :=
    avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
  obtain ⟨E, hMeasE, hPosE, hTube⟩ :=
    avram_gaussianB_canonical_measurable_positive_joint_long_tube
  exact ⟨𝓕, Y, hpath, hStand, hUBV, hAdm,
    E, hMeasE, hPosE, hTube⟩
