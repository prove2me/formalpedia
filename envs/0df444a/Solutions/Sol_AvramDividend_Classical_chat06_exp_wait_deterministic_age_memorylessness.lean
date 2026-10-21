-- Prove2me | solution 1 for AvramDividend.Classical.chat06_exp_wait_deterministic_age_memorylessness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:40:48.795988+00:00
-- url     : https://prove2.me/submissions/53fd511d-8842-42e3-a80f-f142acc2840c

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

namespace AvramChat06

/-- Deterministic-age memorylessness in real probabilities.
This is the identity needed to condition on the current age
of an exponential interarrival time. The next problem is
passing from deterministic age to the random age determined
by an arbitrary observed waiting-time history. -/
theorem exp_wait_survival_ratio
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℝ)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P.real {ω | u < τ ω} = Real.exp (-u))
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    P.real {ω | a + t < τ ω} =
      P.real {ω | a < τ ω} * Real.exp (-t) := by
  calc
    P.real {ω | a + t < τ ω} =
        Real.exp (-(a + t)) := hTail (a + t) (add_nonneg ha ht)
    _ = Real.exp (-a) * Real.exp (-t) := by
      rw [show -(a + t) = -a + -t by ring, Real.exp_add]
    _ = P.real {ω | a < τ ω} * Real.exp (-t) := by
      rw [hTail a ha]

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℝ)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P.real {ω | u < τ ω} = Real.exp (-u))
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    P.real {ω | a + t < τ ω} =
      P.real {ω | a < τ ω} * Real.exp (-t) := by
  exact exp_wait_survival_ratio P τ hTail a t ha ht
