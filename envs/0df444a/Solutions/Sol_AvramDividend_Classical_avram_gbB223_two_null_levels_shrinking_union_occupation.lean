-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB223_two_null_levels_shrinking_union_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:53:24.606346+00:00
-- url     : https://prove2.me/submissions/58b4ba17-c34f-43f8-afa9-d46ed6a661f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB194_shrinking_band_from_null_level_measurable_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Occupation of two shrinking neighbourhoods tends to zero. -/
theorem solution
    (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) (ρ a b : ℝ)
    (ha : volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = a} = 0)
    (hb : volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = b} = 0) :
    Tendsto (fun k : ℕ =>
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        (abs (f t - a) < (1 : ℝ) / ((k : ℝ) + 1) ∨
         abs (f t - b) < (1 : ℝ) / ((k : ℝ) + 1))})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let A : ℕ → Set ℝ := fun k =>
    {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
      abs (f t - a) < (1 : ℝ) / ((k : ℝ) + 1)}
  let B : ℕ → Set ℝ := fun k =>
    {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
      abs (f t - b) < (1 : ℝ) / ((k : ℝ) + 1)}
  have hA : Tendsto (fun k : ℕ => volume (A k))
      atTop (𝓝 (0 : ℝ≥0∞)) :=
    avram_gbB194_shrinking_band_from_null_level_measurable_path
      f hf n ρ a ha
  have hB : Tendsto (fun k : ℕ => volume (B k))
      atTop (𝓝 (0 : ℝ≥0∞)) :=
    avram_gbB194_shrinking_band_from_null_level_measurable_path
      f hf n ρ b hb
  have hU : Tendsto (fun k : ℕ =>
      volume (A k) + volume (B k))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [add_zero] using hA.add hB
  have hBound (k : ℕ) :
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
          (abs (f t - a) < (1 : ℝ) / ((k : ℝ) + 1) ∨
           abs (f t - b) < (1 : ℝ) / ((k : ℝ) + 1))} ≤
        volume (A k) + volume (B k) := by
    have heq :
        {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
          (abs (f t - a) < (1 : ℝ) / ((k : ℝ) + 1) ∨
           abs (f t - b) < (1 : ℝ) / ((k : ℝ) + 1))} =
        (A k ∪ B k) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_union, A, B]
      tauto
    rw [heq]
    exact measure_union_le _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hU
    (fun k => bot_le)
    hBound

