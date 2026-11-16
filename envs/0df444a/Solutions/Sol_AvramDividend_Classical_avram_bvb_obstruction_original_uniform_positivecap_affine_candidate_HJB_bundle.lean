-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_uniform_positivecap_affine_candidate_HJB_bundle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:50:40.291334+00:00
-- url     : https://prove2.me/submissions/08e292ad-162d-471a-b254-c3db8969b8b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_candidate_continuous_on_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_candidate_strict_interior_C1
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_positive_reserve_deriv_eq_one
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_GeneratorIntegrable_half_affine
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_mark_generator_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_generator_HJB_of_uniform_mark_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))
    (hσ : X.σ = 0) (hc : X.c = 1 / 2)
    (C : ℝ≥0∞) :
    let w : ℝ → ℝ := fun u => if u < 0 then 0 else 1 / 2 + u
    ContinuousOn w (Ici 0) ∧
    0 ≤ w 0 ∧
    (∀ z : ℝ, z < 0 → w z = 0) ∧
    ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) := by
  dsimp
  let w : ℝ → ℝ := fun u => if u < 0 then 0 else 1 / 2 + u
  have hw : ∀ u : ℝ, w u = if u < 0 then 0 else 1 / 2 + u := by
    intro u
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [w] using
      avram_bvb_obstruction_half_affine_candidate_continuous_on_nonnegative
  · simp [w]
  · intro z hz
    simp [w, hz]
  · simpa [w] using
      avram_bvb_obstruction_half_affine_candidate_strict_interior_C1 C
  · intro y hy hCap
    have hd : deriv w y = 1 := by
      simpa [w] using
        avram_bvb_obstruction_half_affine_positive_reserve_deriv_eq_one y hy
    have hv : w y = 1 / 2 + y := by
      simp [hw y, not_lt.mpr (le_of_lt hy)]
    have hjump :=
      avram_bvb_obstruction_original_uniform_mark_generator_integral_exact
        X hν y hy w hw hd
    exact ⟨avram_bvb_obstruction_original_uniform_GeneratorIntegrable_half_affine
        X hν y hy w hw hd,
      avram_bvb_obstruction_generator_HJB_of_uniform_mark_kernel
        X y hy w hσ hc hv hd hjump⟩
  · intro y hy hCap
    have hd : deriv w y = 1 := by
      simpa [w] using
        avram_bvb_obstruction_half_affine_positive_reserve_deriv_eq_one y hy
    rw [hd]
