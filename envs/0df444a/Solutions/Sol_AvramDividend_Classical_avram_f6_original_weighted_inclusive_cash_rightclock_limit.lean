-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_weighted_inclusive_cash_rightclock_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:24:17.527188+00:00
-- url     : https://prove2.me/submissions/f77961bb-418b-4ce5-b0c4-16c37ffd96fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_real_cash_antitone_physical_clock_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (A : Set ℝ) (hA : MeasurableSet A)
    (a : ℕ → ℝ) (s : ℝ) (ha : Antitone a)
    (hl : Tendsto a atTop (𝓝 s))
    (hfinite : ∃ n,
      (∫⁻ t in A ∩ Iic (a n), f t ∂μ) ≠ ∞) :
    Tendsto
      (fun n => (∫⁻ t in A ∩ Iic (a n), f t ∂μ).toReal)
      atTop (𝓝 ((∫⁻ t in A ∩ Iic s, f t ∂μ).toReal)) := by
  let ν : Measure ℝ := (μ.withDensity f).restrict A
  have hν (z : ℝ) :
      ν (Iic z) = ∫⁻ t in A ∩ Iic z, f t ∂μ := by
    dsimp [ν]
    rw [Measure.restrict_apply measurableSet_Iic]
    rw [withDensity_apply f (measurableSet_Iic.inter hA)]
    rw [inter_comm]
  obtain ⟨i, hi⟩ := hfinite
  have hfiniteν : ∃ i, ν (Iic (a i)) ≠ ∞ :=
    ⟨i, by simpa only [hν] using hi⟩
  simpa only [hν] using
    (avram_f6_original_real_cash_antitone_physical_clock_limit
      ν a s ha hl hfiniteν)
