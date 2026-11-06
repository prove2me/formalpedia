-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_bv_original_C1_path_and_right_jump_premises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:10:37.649817+00:00
-- url     : https://prove2.me/submissions/ff65c322-069c-4f30-8731-5d5adb6e4e02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original admissibility and the C1 slope bound discharge both pathwise
    source premises of the BV signed-Fatou grid theorem at every cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici (0 : ℝ))) (hw0 : 0 ≤ w 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) ∧
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω))) := by
  intro x hx hxC D hD
  have hPos := avram_p3_bv_initial_value_nonnegative
    C hC w hwCont hw0 hwSmooth hwGrad
  constructor
  · intro ω t htpos ht
    obtain ⟨hrisk, hcap⟩ :=
      capped_riskProcess_range_before_ruin_including_zero
        X x hx C hxC D hD ω t ht
    exact hPos _ hrisk hcap
  · exact avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
      X C hC w hwCont hwSmooth hwGrad x hxC D hD
