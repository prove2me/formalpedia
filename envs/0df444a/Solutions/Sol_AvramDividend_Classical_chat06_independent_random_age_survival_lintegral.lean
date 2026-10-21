-- Prove2me | solution 1 for AvramDividend.Classical.chat06_independent_random_age_survival_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:16:34.216333+00:00
-- url     : https://prove2.me/submissions/8f732284-490d-40bd-95e2-ce4fd9470956

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- An exact, unrestricted random-age survival identity. Under
independence the survival probability is the integral, over the
complete law of the observed age, of the deterministic threshold
survival probability of the waiting time. No finite-support or
discretisation assumption occurs. -/
theorem independent_random_age_survival_lintegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A τ : Ω → ℝ) (hA : Measurable A)
    (hτ : Measurable τ) (hInd : IndepFun A τ P)
    (t : ℝ) :
    P {ω | A ω + t < τ ω} =
      ∫⁻ a, (P.map τ) (Ioi (a + t)) ∂(P.map A) := by
  let E : Set (ℝ × ℝ) := {p | p.1 + t < p.2}
  have hm : MeasurableSet E := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | t < p.2 - p.1} :=
      (measurable_snd.sub measurable_fst) measurableSet_Ioi
    have hEq : E = {p : ℝ × ℝ | t < p.2 - p.1} := by
      ext p
      change (p.1 + t < p.2) ↔ (t < p.2 - p.1)
      constructor <;> intro h <;> linarith
    rw [hEq]
    exact hmeas
  have hIndProd :
      P.map (fun ω => (A ω, τ ω)) =
        (P.map A).prod (P.map τ) :=
    hInd.map_prod_eq_prod_map_map hA.aemeasurable hτ.aemeasurable
  calc
    P {ω | A ω + t < τ ω} =
        (P.map (fun ω => (A ω, τ ω))) E := by
      rw [Measure.map_apply (hA.prodMk hτ) hm]
      rfl
    _ = ((P.map A).prod (P.map τ)) E := by rw [hIndProd]
    _ = ∫⁻ a, (P.map τ) (Ioi (a + t)) ∂(P.map A) := by
      rw [Measure.prod_apply hm]
      rfl

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A τ : Ω → ℝ) (hA : Measurable A)
    (hτ : Measurable τ) (hInd : IndepFun A τ P)
    (t : ℝ) :
    P {ω | A ω + t < τ ω} =
      ∫⁻ a, (P.map τ) (Ioi (a + t)) ∂(P.map A) := by
  exact independent_random_age_survival_lintegral
    A τ hA hτ hInd t
