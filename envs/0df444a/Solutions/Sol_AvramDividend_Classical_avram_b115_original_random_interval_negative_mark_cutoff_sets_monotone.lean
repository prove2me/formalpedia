-- Prove2me | solution 1 for AvramDividend.Classical.avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T16:19:30.044517+00:00
-- url     : https://prove2.me/submissions/fc74ef7d-7689-4730-b624-79c122f057d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Prescribed negative-mark cutoff jump-time sets are monotone for the same original source physical interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    {u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))} ⊆
    {u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((m : ℝ) + 1))} := by
  intro u hu
  have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hcut :
      -(1 / ((n : ℝ) + 1)) ≤ -(1 / ((m : ℝ) + 1)) := by
    gcongr
  exact ⟨hu.1, hu.2.1, le_trans hu.2.2 hcut⟩
