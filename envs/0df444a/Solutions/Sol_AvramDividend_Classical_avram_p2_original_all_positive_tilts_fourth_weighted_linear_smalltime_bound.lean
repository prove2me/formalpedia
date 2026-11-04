-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_all_positive_tilts_fourth_weighted_linear_smalltime_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:18:59.07999+00:00
-- url     : https://prove2.me/submissions/11519e6b-e9aa-4f68-b15c-652d40099bfe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every nonnegative exponential tilt of the original fourth jump-deficit
moment is O(h) as h decreases to zero; provides all tilted weighted moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
          (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) ≤
          C * h := by
  have hlim : Tendsto
      (fun h : ℝ =>
        (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
          (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), Real.exp (ρ * y) *
        (Real.exp y - 1) ^ 4 ∂X.ν)) := by
    simpa only [one_mul] using
      (avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
        X ρ 1 hρ zero_le_one)
  let L : ℝ := ∫ y in Iio (0 : ℝ), Real.exp (ρ * y) *
    (Real.exp y - 1) ^ 4 ∂X.ν
  let C : ℝ := max 1 (L + 1)
  refine ⟨C, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_left 1 (L + 1)), ?_⟩
  have hnear : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
        (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h < L + 1 := by
    have hnhds : Iio (L + 1) ∈ nhds L :=
      isOpen_Iio.mem_nhds (by simp)
    exact hlim.eventually hnhds
  have hpos : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      h ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  filter_upwards [hnear, hpos] with h hh hh0
  have hle :
      (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
        (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h ≤ C :=
    (le_of_lt hh).trans (le_max_right 1 (L + 1))
  calc
    (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
      (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) =
      ((∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
        (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h) * h := by
          have hpositive : 0 < h := Set.mem_Ioi.mp hh0
          field_simp [ne_of_gt hpositive] <;> ring
    _ ≤ C * h := mul_le_mul_of_nonneg_right hle (le_of_lt (Set.mem_Ioi.mp hh0))
