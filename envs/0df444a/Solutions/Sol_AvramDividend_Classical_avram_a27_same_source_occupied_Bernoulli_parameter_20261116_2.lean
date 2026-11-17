-- Prove2me | solution 2 for AvramDividend.Classical.avram_a27_same_source_occupied_Bernoulli_parameter_20261116
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:30:54.298663+00:00
-- url     : https://prove2.me/submissions/5b0a1b52-4a7a-4642-8c80-526ecdfbba82

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_same_source_occupied_Bernoulli_parameter_20261116
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
  rw [hSame i, hp]
  have hm : MeasurableSet {ω : Ω | C ω = 0} := (measurableSet_singleton 0).preimage hC
  have : {ω : Ω | C ω ≠ 0} = {ω : Ω | C ω = 0}ᶜ := rfl
  rw [this, prob_compl_eq_one_sub hm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one]

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℕ)
    (C : Ω → ℝ≥0∞) (hC : Measurable C)
    (hSame : ∀ i : Fin n,
      P {ω : Ω | Y i ω = 1} = P {ω : Ω | C ω ≠ 0})
    (p : unitInterval)
    (hp : (p : ℝ) = 1 - (P {ω : Ω | C ω = 0}).toReal) :
    ∀ i : Fin n, (P {ω : Ω | Y i ω = 1}).toReal = (p : ℝ) :=
  AvramDividend.Classical.avram_a27_same_source_occupied_Bernoulli_parameter_20261116 P n Y C hC hSame p hp
