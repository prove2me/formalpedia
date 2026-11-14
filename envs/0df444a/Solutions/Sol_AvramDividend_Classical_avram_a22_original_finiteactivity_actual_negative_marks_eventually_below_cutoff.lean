-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_finiteactivity_actual_negative_marks_eventually_below_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T17:57:17.354536+00:00
-- url     : https://prove2.me/submissions/4d794398-8b8e-4770-a4a3-bff5f3afddd1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- On the true original source each nonzero negative mark is eventually below the narrowing negative cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ u : ℝ≥0, 0 < u → u ≤ t →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1)) := by
  have hGap :=
    avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
      X hFinite
  filter_upwards [hGap] with ω hω
  intro t
  obtain ⟨N, hN⟩ := hω t
  refine ⟨N, ?_⟩
  intro n hn u hu ht hju
  have hSign :=
    avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu
  have hTiny := hN n hn u hu ht
  by_contra hnot
  have hlt : -(1 / ((n : ℝ) + 1)) <
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u :=
    lt_of_not_ge hnot
  have habs :
      |X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u| ≤
        1 / ((n : ℝ) + 1) := by
    rw [abs_of_nonpos hSign]
    linarith
  exact hju (hTiny habs)
