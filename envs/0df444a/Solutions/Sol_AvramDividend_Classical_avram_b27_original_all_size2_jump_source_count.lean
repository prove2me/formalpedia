-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_all_size2_jump_source_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:51:35.729918+00:00
-- url     : https://prove2.me/submissions/6ed29474-fa8d-4358-8e33-3137d50327cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_tsum_finite_support
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0)
    (hSize : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = -2)) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
        -2 * (F.card : ℝ) := by
  classical
  obtain ⟨F, hF, _⟩ :=
    avram_p4_h_gaussian_original_largejump_tsum_finite_support X ω t
  have hFexact : ∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    intro u
    constructor
    · intro hu
      rcases (hF u).mp hu with ⟨hpos, ht, hlarge⟩
      refine ⟨hpos, ht, ?_⟩
      intro hz
      linarith
    · rintro ⟨hpos, ht, hnot⟩
      rcases hSize u hpos with hz | htwo
      · exact False.elim (hnot hz)
      · apply (hF u).mpr
        refine ⟨hpos, ht, ?_⟩
        change X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1
        linarith [htwo]
  have hSizeF : ∀ u ∈ F,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = -2 := by
    intro u hu
    rcases (hF u).mp hu with ⟨hpos, ht, hlarge⟩
    rcases hSize u hpos with hz | htwo
    · linarith
    · exact htwo
  refine ⟨F, hFexact, ?_⟩
  have hRaw :=
    avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
      X ω t F hFexact
  calc
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      ∑ u ∈ F,
        if X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        else 0 := hRaw
    _ = ∑ u ∈ F, (-2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hmark := hSizeF u hu
      simp [hmark]
    _ = -2 * (F.card : ℝ) := by
      simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
      ring
