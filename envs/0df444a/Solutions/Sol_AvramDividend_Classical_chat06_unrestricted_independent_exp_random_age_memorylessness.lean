-- Prove2me | solution 1 for AvramDividend.Classical.chat06_unrestricted_independent_exp_random_age_memorylessness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:44:05.401765+00:00
-- url     : https://prove2.me/submissions/37235cd5-f948-4dbc-a404-c46a89c32db6

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_independent_random_age_survival_lintegral
import Theorems.Thm_AvramDividend_Classical_chat06_exponential_random_age_lintegral_scaling

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- Exact unrestricted residual-wait memorylessness at a random,
nonnegative, measurable observed age A, independent of a unit
exponential waiting time. Finite age support is not assumed:
joint-law product structure plus Tonelli and the exponential
tail kernel's multiplicative identity handle the continuum. -/
theorem independent_exp_wait_random_age_survival
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A τ : Ω → ℝ)
    (hA : Measurable A) (hτ : Measurable τ)
    (hInd : IndepFun A τ P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ A ω)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | A ω + t < τ ω} =
      P {ω | A ω < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  have hMapNonneg : ∀ᵐ a ∂(P.map A), 0 ≤ a :=
    (ae_map_iff hA.aemeasurable measurableSet_Ici).2 hNonneg
  have hTailMap (u : ℝ) (hu : 0 ≤ u) :
      (P.map τ) (Ioi u) = ENNReal.ofReal (Real.exp (-u)) := by
    rw [Measure.map_apply hτ measurableSet_Ioi]
    exact hTail u hu
  have hZero :
      P {ω | A ω < τ ω} =
        ∫⁻ a, (P.map τ) (Ioi a) ∂(P.map A) := by
    simpa only [add_zero] using
      (AvramDividend.Classical.chat06_independent_random_age_survival_lintegral
        A τ hA hτ hInd 0)
  calc
    P {ω | A ω + t < τ ω} =
        ∫⁻ a, (P.map τ) (Ioi (a + t)) ∂(P.map A) :=
      AvramDividend.Classical.chat06_independent_random_age_survival_lintegral
        A τ hA hτ hInd t
    _ = (∫⁻ a, (P.map τ) (Ioi a) ∂(P.map A)) *
          ENNReal.ofReal (Real.exp (-t)) :=
      AvramDividend.Classical.chat06_exponential_random_age_lintegral_scaling
        (P.map A) (P.map τ) t ht hMapNonneg hTailMap
    _ = P {ω | A ω < τ ω} *
          ENNReal.ofReal (Real.exp (-t)) := by rw [hZero]

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A τ : Ω → ℝ)
    (hA : Measurable A) (hτ : Measurable τ)
    (hInd : IndepFun A τ P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ A ω)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | A ω + t < τ ω} =
      P {ω | A ω < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  exact independent_exp_wait_random_age_survival
    A τ hA hτ hInd hNonneg hTail t ht
