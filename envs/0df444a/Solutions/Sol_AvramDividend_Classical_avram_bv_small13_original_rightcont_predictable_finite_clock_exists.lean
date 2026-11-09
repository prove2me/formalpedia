-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_small13_original_rightcont_predictable_finite_clock_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:38:08.981768+00:00
-- url     : https://prove2.me/submissions/9d65c91a-25c7-4b08-a4ba-57ce88e1a0a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_original_finite_horizon_predictable_intensity_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original right-continuous predictable time-probability law has a
source-exact finite-horizon measure witness, with no HJB or shift hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A := by
  have h := avram_wave4_04_original_finite_horizon_predictable_intensity_budget
    X x D hD (fun _ : ℝ => (0 : ℝ)) (-1) 2 0 1 (1 / 2)
    (by fun_prop) (by fun_prop) (by intros; rfl)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) T
  rcases h with ⟨μ, hfinite, hclock, _⟩
  exact ⟨μ, hfinite, hclock⟩
