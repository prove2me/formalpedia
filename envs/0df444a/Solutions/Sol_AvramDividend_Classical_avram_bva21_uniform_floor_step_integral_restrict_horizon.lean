-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_uniform_floor_step_integral_restrict_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:02:44.452845+00:00
-- url     : https://prove2.me/submissions/95040dff-a16f-40fe-8cf3-86047a90d8d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- The original inclusive uniform floor grid is supported on its finite horizon. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) :
    (∫ t : ℝ,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) =
    ∫ t in Set.Icc (0 : ℝ) T,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by
  let f : ℝ → ℝ := fun t =>
    if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
    then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hinner :
      T * ((n : ℝ) + 1) / ((n : ℝ) + 2) < T := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [hT]
  have hzero (t : ℝ) (ht : t ∉ Icc (0 : ℝ) T) : f t = 0 := by
    dsimp [f]
    split_ifs with hc
    · exact False.elim (ht ⟨hc.1, le_trans (le_of_lt hc.2) hinner.le⟩)
    · rfl
  have hcongr :
      (∫ t : ℝ, f t) =
      (∫ t : ℝ, (Icc (0 : ℝ) T).indicator f t) := by
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Icc (0 : ℝ) T
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht, hzero t ht]
  have hid :
      (∫ t : ℝ, (Icc (0 : ℝ) T).indicator f t) =
      (∫ t in Icc (0 : ℝ) T, f t) :=
    integral_indicator measurableSet_Icc
  simpa only [f] using hcongr.trans hid
