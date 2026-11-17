-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_probability_void_complement_is_unitInterval_parameter_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:41:17.285306+00:00
-- url     : https://prove2.me/submissions/84286f87-157e-43ec-b05a-3d217e23e2c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Set Ω) :
    ∃ p : ℕ → unitInterval,
      ∀ n : ℕ, (p n : ℝ) = 1 - (P (E n)).toReal := by
  let p : ℕ → unitInterval := fun n => ⟨1 - (P (E n)).toReal, by
    have hle : (P (E n)).toReal ≤ 1 := by
      have hh : P (E n) ≤ (1 : ℝ≥0∞) := by
        calc
          P (E n) ≤ P Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hfin : (1 : ℝ≥0∞) ≠ ⊤ := by simp
      have ht := ENNReal.toReal_mono hfin hh
      simpa using ht
    have hnon : 0 ≤ (P (E n)).toReal := ENNReal.toReal_nonneg
    exact ⟨by linarith, by linarith⟩⟩
  exact ⟨p, by intro n; rfl⟩
