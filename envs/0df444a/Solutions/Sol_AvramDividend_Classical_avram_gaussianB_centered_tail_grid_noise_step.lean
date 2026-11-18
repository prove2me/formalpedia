-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_centered_tail_grid_noise_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:45:03.013209+00:00
-- url     : https://prove2.me/submissions/fa2cf1d1-a899-4fae-ae1b-d0a99fb75969

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section
/-- Centered original source mesh control through one extra physical grid cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hc : X.c = 2)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 500 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 500 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (n m : ℕ)
    (hStep : (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) ≤ (1 / 1000 : ℝ≥0))
    (s : ℝ≥0)
    (hs : s ≤ (1 / 1000 : ℝ≥0) +
      (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) :
    |X.X s ω - (s : ℝ) * X.c| ≤ (1 / 4000 : ℝ) := by
  have hsLong : s ≤ (1 / 500 : ℝ≥0) := by
    calc
      s ≤ (1 / 1000 : ℝ≥0) +
          (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) := hs
      _ ≤ (1 / 1000 : ℝ≥0) + (1 / 1000 : ℝ≥0) :=
        add_le_add le_rfl hStep
      _ = (1 / 500 : ℝ≥0) := by norm_num
  have hSrc := hSource s hsLong
  calc
    |X.X s ω - (s : ℝ) * X.c| = |B s| := by
      rw [hSrc, hc]
      congr 1
      ring
    _ ≤ (1 / 4000 : ℝ) := hCentered s hsLong
