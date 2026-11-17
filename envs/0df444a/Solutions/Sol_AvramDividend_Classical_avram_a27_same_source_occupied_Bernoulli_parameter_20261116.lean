-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_same_source_occupied_Bernoulli_parameter_20261116
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:29:56.109204+00:00
-- url     : https://prove2.me/submissions/9a2f39ab-59e4-418e-8f0c-895c4f076b8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_prob_nonzero_real_eq_one_sub_void_20261116
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
  rw [avram_a27_prob_nonzero_real_eq_one_sub_void_20261116 P C hC (0 : ℝ≥0∞)]
  exact hp.symm
