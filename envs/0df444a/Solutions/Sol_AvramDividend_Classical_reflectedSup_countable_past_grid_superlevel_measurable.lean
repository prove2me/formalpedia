-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_countable_past_grid_superlevel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:05:24.801189+00:00
-- url     : https://prove2.me/submissions/8b0b1761-bb7f-4133-a2d2-ba04a3fdbafa

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.Process.Adapted
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (t : ℝ≥0)
    (hclock : ∀ n : ℕ, clock n ≤ t) (x : ℝ) :
    MeasurableSet[𝓕 t]
      {ω : Ω | ∃ n : ℕ, x ≤ reflectedSup X (clock n) ω} := by
  have hMeas : ∀ n : ℕ, MeasurableSet[𝓕 t]
      {ω : Ω | x ≤ reflectedSup X (clock n) ω} := by
    intro n
    have hAt : Measurable[𝓕 t]
        (fun ω : Ω => reflectedSup X (clock n) ω) :=
      ((reflectedSup_adapted X) (clock n)).mono
        (𝓕.mono (hclock n)) le_rfl
    exact measurableSet_le measurable_const hAt
  have hUnion : MeasurableSet[𝓕 t]
      (⋃ n : ℕ, {ω : Ω | x ≤ reflectedSup X (clock n) ω}) :=
    MeasurableSet.iUnion hMeas
  convert hUnion using 1
  ext ω
  simp
