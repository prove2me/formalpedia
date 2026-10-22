-- Prove2me | solution 1 for AvramDividend.Classical.chat06_iid_random_count_residual_full_future_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:43:23.606192+00:00
-- url     : https://prove2.me/submissions/cf910b0f-172d-4a28-b112-9c88ed4f5bc5

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_count_event_residual_future_joint
import Theorems.Thm_AvramDividend_Classical_chat06_selected_residual_future_joint_of_countwise_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Complete joint survival/event law of the residual wait and all
post-next-claim waits after selecting the count at a fixed clock. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℕ) (hN : Measurable N)
    (clock t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount : ∀ n : ℕ,
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | t < τ (N ω) ω -
      (clock - ∑ i ∈ Finset.range (N ω), τ i ω) ∧
      (fun j : ℕ => τ (N ω + 1 + j) ω) ∈ B} =
        ENNReal.ofReal (Real.exp (-t)) * μ B := by
  let F : ℕ → Ω → ℝ := fun n ω =>
    τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)
  let G : ℕ → Ω → (ℕ → ℝ) :=
    fun n ω j => τ (n + 1 + j) ω
  have hF : ∀ n, Measurable (F n) := by
    intro n
    exact (hτ n).sub (measurable_const.sub
      (Finset.measurable_sum _ fun i _ => hτ i))
  have hG : ∀ n, Measurable (G n) := by
    intro n
    apply measurable_pi_lambda
    intro j
    exact hτ (n + 1 + j)
  have hFactor (n : ℕ) :
      P {ω | N ω = n ∧ t < F n ω ∧ G n ω ∈ B} =
        (P {ω | N ω = n} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := by
    exact
      AvramDividend.Classical.chat06_indexed_count_event_residual_future_joint
        τ hτ hiid n N clock t ht μ (hLaw n) B hB
        (hTail n) (hCount n)
  exact
    AvramDividend.Classical.chat06_selected_residual_future_joint_of_countwise_factorisation
      N hN F hF G hG B hB t
      (ENNReal.ofReal (Real.exp (-t))) (μ B) hFactor
