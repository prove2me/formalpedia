-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_same_source_ENNReal_occupied_Bernoulli_parameter_corrected_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:33:49.410268+00:00
-- url     : https://prove2.me/submissions/16d3b98f-9a17-4e5c-9e2d-250535e8b3c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_ENNReal_count_nonzero_probability_complement_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℕ)
    (C : Ω → ℝ≥0∞) (hC : Measurable C)
    (hSame : ∀ i : Fin n,
      P {ω : Ω | Y i ω = 1} = P {ω : Ω | C ω ≠ 0})
    (p : unitInterval)
    (hp : (p : ℝ) = 1 - (P {ω : Ω | C ω = 0}).toReal) :
    ∀ i : Fin n, (P {ω : Ω | Y i ω = 1}).toReal = (p : ℝ) := by
  intro i
  rw [hSame i]
  rw [avram_a27_original_ENNReal_count_nonzero_probability_complement_20261116 P C hC]
  exact hp.symm
