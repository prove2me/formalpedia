-- Prove2me | solution 1 for AvramDividend.Classical.zero_probability_of_poisson_count_no_jump_event
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:59:20.254985+00:00
-- url     : https://prove2.me/submissions/1f280f0c-fba5-485a-bdd7-fe1275e81fe0

import Theorems.Thm_AvramDividend_Classical_zero_probability_of_diverging_poisson_zero_count_bounds
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
open AvramDividend.Classical MeasureTheory Set Filter
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (counts : ℕ → Ω → ℕ) (rates : ℕ → ℝ)
    (hrates : Tendsto rates atTop atTop)
    (hsubset : ∀ n : ℕ, A ⊆ {ω | counts n ω = 0})
    (hzeroLaw : ∀ n : ℕ,
      P {ω | counts n ω = 0} = ENNReal.ofReal (Real.exp (-(rates n)))) :
    P A = 0 := by
  refine zero_probability_of_diverging_poisson_zero_count_bounds P A rates hrates fun n => ?_
  have h := measure_mono (μ := P) (hsubset n)
  rw [hzeroLaw n] at h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
