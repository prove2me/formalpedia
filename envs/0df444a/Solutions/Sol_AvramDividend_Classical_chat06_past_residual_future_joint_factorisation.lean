-- Prove2me | solution 1 for AvramDividend.Classical.chat06_past_residual_future_joint_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:51:32.100505+00:00
-- url     : https://prove2.me/submissions/20afef5f-35e3-4a9b-9fc5-37896848f271

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- Combine residual waiting-time survival on an observed-past event
with independence of the complete waiting-time/future-suffix pair.
The residual factorisation remains an explicit hypothesis. -/
theorem past_residual_future_joint_factorisation
    {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → E) (τ : Ω → ℝ) (Fut : Ω → F)
    (hInd : IndepFun (fun ω => (Z ω, τ ω)) Fut P)
    (μ : Measure F) (hLaw : HasLaw Fut μ P)
    (age : E → ℝ) (hAge : Measurable age)
    (D : Set E) (hD : MeasurableSet D)
    (B : Set F) (hB : MeasurableSet B)
    (t : ℝ) (c : ℝ≥0∞)
    (hResidual :
      P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ ω} =
        P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} * c) :
    P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ ω) ∧ Fut ω ∈ B} =
      (P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} * c) * μ B := by
  let Q : Set (E × ℝ) :=
    {p | p.1 ∈ D ∧ age p.1 + t < p.2}
  have hQ : MeasurableSet Q := by
    have hDiff : Measurable (fun p : E × ℝ =>
        p.2 - age p.1) :=
      measurable_snd.sub (hAge.comp measurable_fst)
    have hLt : MeasurableSet {p : E × ℝ |
        t < p.2 - age p.1} := hDiff measurableSet_Ioi
    have hEq : {p : E × ℝ | age p.1 + t < p.2} =
        {p : E × ℝ | t < p.2 - age p.1} := by
      ext p
      change (age p.1 + t < p.2) ↔ (t < p.2 - age p.1)
      constructor <;> intro h <;> linarith
    change MeasurableSet
      ({p : E × ℝ | p.1 ∈ D} ∩
        {p : E × ℝ | age p.1 + t < p.2})
    exact (measurable_fst hD).inter (hEq ▸ hLt)
  have hFactor :=
    hInd.measure_inter_preimage_eq_mul Q B hQ hB
  have hFutureLaw : P {ω | Fut ω ∈ B} = μ B :=
    hLaw.measure_eq hB
  calc
    P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ ω) ∧ Fut ω ∈ B} =
        P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ ω} *
          P {ω | Fut ω ∈ B} := hFactor
    _ = (P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} * c) *
          μ B := by rw [hResidual, hFutureLaw]

end AvramChat06

open AvramChat06

theorem solution
    {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → E) (τ : Ω → ℝ) (Fut : Ω → F)
    (hInd : IndepFun (fun ω => (Z ω, τ ω)) Fut P)
    (μ : Measure F) (hLaw : HasLaw Fut μ P)
    (age : E → ℝ) (hAge : Measurable age)
    (D : Set E) (hD : MeasurableSet D)
    (B : Set F) (hB : MeasurableSet B)
    (t : ℝ) (c : ℝ≥0∞)
    (hResidual :
      P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ ω} =
        P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} * c) :
    P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ ω) ∧ Fut ω ∈ B} =
      (P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} * c) * μ B := by
  exact past_residual_future_joint_factorisation
    Z τ Fut hInd μ hLaw age hAge D hD B hB t c hResidual
