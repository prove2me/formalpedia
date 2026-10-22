-- Prove2me | solution 1 for AvramDividend.Classical.chat06_indexed_iid_past_residual_full_future_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:16:51.471326+00:00
-- url     : https://prove2.me/submissions/82f434e2-13e8-4534-941d-63fb7625efbd

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_prefix_current_wait_future_independent
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_wait_prefix_random_age_residual
import Theorems.Thm_AvramDividend_Classical_chat06_past_residual_future_joint_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- A past event, the exponential residual of the current wait,
and an arbitrary event of the whole future waiting suffix have
their exact joint probability at each deterministic index. -/
theorem indexed_iid_past_residual_full_future_joint_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (age : (ℕ → ℝ) → ℝ) (hAge : Measurable age)
    (D B : Set (ℕ → ℝ)) (hD : MeasurableSet D)
    (hB : MeasurableSet B)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ n ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
        ENNReal.ofReal (Real.exp (-t))) * μ B := by
  let Fut : Ω → (ℕ → ℝ) :=
    fun ω j => τ (n + 1 + j) ω
  have hInd : IndepFun (fun ω => (Z ω, τ n ω)) Fut P := by
    rw [hZ]
    simpa only [Fut] using
      (AvramDividend.Classical.chat06_indexed_iid_prefix_current_wait_future_independent
        τ hτ hiid n)
  have hResidual :=
    AvramDividend.Classical.chat06_indexed_iid_wait_prefix_random_age_residual
      τ hτ hiid n Z hZ age hAge D hD hNonneg hTail t ht
  exact
    AvramDividend.Classical.chat06_past_residual_future_joint_factorisation
      Z (τ n) Fut hInd μ hLaw age hAge D hD B hB t
      (ENNReal.ofReal (Real.exp (-t))) hResidual

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (age : (ℕ → ℝ) → ℝ) (hAge : Measurable age)
    (D B : Set (ℕ → ℝ)) (hD : MeasurableSet D)
    (hB : MeasurableSet B)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ n ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
        ENNReal.ofReal (Real.exp (-t))) * μ B := by
  exact indexed_iid_past_residual_full_future_joint_law
    τ hτ hiid n Z hZ age hAge D B hD hB μ hLaw hNonneg hTail t ht
