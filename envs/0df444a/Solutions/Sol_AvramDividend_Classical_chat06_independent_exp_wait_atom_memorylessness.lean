-- Prove2me | solution 1 for AvramDividend.Classical.chat06_independent_exp_wait_atom_memorylessness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:58:25.724493+00:00
-- url     : https://prove2.me/submissions/24d16d6c-6786-4730-b9ee-afb5c72320a8

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- A complete past observable A independent of an exponential
wait τ has a fixed-age survival factorisation on each atom A=a.
This is a measurable-cylinder precursor to the random-age
memorylessness needed for continuous-time Poisson renewal. -/
theorem independent_exp_wait_fixed_age_survival
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A τ : Ω → ℝ)
    (hInd : IndepFun A τ P)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} =
        ENNReal.ofReal (Real.exp (-u)))
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    P ({ω | A ω = a} ∩ {ω | a + t < τ ω}) =
      P ({ω | A ω = a} ∩ {ω | a < τ ω}) *
        ENNReal.ofReal (Real.exp (-t)) := by
  let E : Set Ω := {ω | A ω = a}
  let F (u : ℝ) : Set Ω := {ω | u < τ ω}
  have hFactor (u : ℝ) :
      P (E ∩ F u) = P E * P (F u) := by
    simpa only [E, F, Set.preimage, Set.mem_setOf_eq,
      Set.mem_singleton_iff, Set.mem_Ioi] using
      (hInd.measure_inter_preimage_eq_mul
        ({a} : Set ℝ) (Set.Ioi u)
        (measurableSet_singleton a) measurableSet_Ioi)
  have hExp :
      ENNReal.ofReal (Real.exp (-(a + t))) =
        ENNReal.ofReal (Real.exp (-a)) *
          ENNReal.ofReal (Real.exp (-t)) := by
    rw [show -(a + t) = -a + -t by ring, Real.exp_add,
      ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  change P (E ∩ F (a + t)) =
    P (E ∩ F a) * ENNReal.ofReal (Real.exp (-t))
  calc
    P (E ∩ F (a + t)) = P E * P (F (a + t)) :=
      hFactor (a + t)
    _ = P E * ENNReal.ofReal (Real.exp (-(a + t))) := by
      rw [show P (F (a + t)) =
        ENNReal.ofReal (Real.exp (-(a + t))) from
        hTail (a + t) (add_nonneg ha ht)]
    _ = P E *
        (ENNReal.ofReal (Real.exp (-a)) *
          ENNReal.ofReal (Real.exp (-t))) := by rw [hExp]
    _ = (P E * P (F a)) *
          ENNReal.ofReal (Real.exp (-t)) := by
      rw [show P (F a) =
        ENNReal.ofReal (Real.exp (-a)) from hTail a ha]
      ac_rfl
    _ = P (E ∩ F a) *
          ENNReal.ofReal (Real.exp (-t)) := by
      rw [hFactor a]

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A τ : Ω → ℝ)
    (hInd : IndepFun A τ P)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} =
        ENNReal.ofReal (Real.exp (-u)))
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    P ({ω | A ω = a} ∩ {ω | a + t < τ ω}) =
      P ({ω | A ω = a} ∩ {ω | a < τ ω}) *
        ENNReal.ofReal (Real.exp (-t)) := by
  exact independent_exp_wait_fixed_age_survival
    P A τ hInd hTail a t ha ht
