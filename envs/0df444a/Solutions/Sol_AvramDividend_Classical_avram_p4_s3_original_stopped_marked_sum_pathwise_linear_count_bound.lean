-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_stopped_marked_sum_pathwise_linear_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:30:05.896528+00:00
-- url     : https://prove2.me/submissions/66d69de3-e26d-4e34-8ebb-73ae5589b6b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original stopped negative-band marked sums obey the pathwise cardinality ceiling. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (τ : Ω → ℝ≥0) (f : Ω → ℝ≥0 → ℝ) (B : ℝ)
    (hf : ∀ ω u, |f ω u| ≤ B) :
    ∀ ω : Ω,
      ‖∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
        X ω (τ ω) n).toFinset, f ω u‖ ≤
        B * ({u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard : ℝ) := by
  classical
  intro ω
  let s : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((n : ℝ) + 1))}
  have hs : s.Finite :=
    avram_wave7_06_original_negative_band_marked_times_finite X ω (τ ω) n
  have hCard : s.ncard = hs.toFinset.card :=
    Set.ncard_eq_toFinset_card s hs
  calc
    ‖∑ u ∈ hs.toFinset, f ω u‖ ≤ ∑ u ∈ hs.toFinset, ‖f ω u‖ :=
      norm_sum_le hs.toFinset (f ω)
    _ ≤ ∑ u ∈ hs.toFinset, B := by
      apply Finset.sum_le_sum
      intro u hu
      simpa only [Real.norm_eq_abs] using hf ω u
    _ = B * ((hs.toFinset).card : ℝ) := by simp [mul_comm]
    _ = B * (s.ncard : ℝ) := by rw [hCard]
