-- Prove2me | solution 1 for AvramDividend.Classical.chat06_iid_random_count_residual_exp_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:27:25.357013+00:00
-- url     : https://prove2.me/submissions/a05f331f-218a-46ab-895d-7f1b862a1c39

import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_fixed_clock_count_residual
import Theorems.Thm_AvramDividend_Classical_chat06_selected_residual_survival_of_countwise_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- The waiting time from a deterministic clock to the next arrival,
selected at the random count index, has the Exp(1) survival law.
The almost-sure count/arrival-cylinder equivalence is explicit. -/
theorem iid_random_count_residual_exp_survival
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℕ) (hN : Measurable N)
    (clock t : ℝ) (ht : 0 ≤ t)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount : ∀ n : ℕ,
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | t < τ (N ω) ω -
      (clock - ∑ i ∈ Finset.range (N ω), τ i ω)} =
        ENNReal.ofReal (Real.exp (-t)) := by
  let F : ℕ → Ω → ℝ := fun n ω =>
    τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)
  have hF : ∀ n, Measurable (F n) := by
    intro n
    exact (hτ n).sub (measurable_const.sub
      (Finset.measurable_sum _ fun i _ => hτ i))
  have hFactor (n : ℕ) :
      P {ω | N ω = n ∧ t < F n ω} =
        P {ω | N ω = n} *
          ENNReal.ofReal (Real.exp (-t)) := by
    have hEvent :
        P {ω | N ω = n ∧ t < F n ω} =
          P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
            clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} := by
      apply measure_congr
      filter_upwards [hCount n] with ω hω
      apply propext
      change (N ω = n ∧
          t < τ n ω -
            (clock - ∑ i ∈ Finset.range n, τ i ω)) ↔
        ((∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω)
      rw [hω, Finset.sum_range_succ]
      constructor
      · rintro ⟨⟨hl, hu⟩, hr⟩
        exact ⟨hl, by linarith⟩
      · rintro ⟨hl, hr⟩
        refine ⟨⟨hl, by linarith⟩, by linarith⟩
    have hBase :
        P {ω | N ω = n} =
          P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
            clock < ∑ i ∈ Finset.range (n + 1), τ i ω} :=
      measure_congr (hCount n)
    rw [hEvent,
      AvramDividend.Classical.chat06_indexed_iid_fixed_clock_count_residual
        τ hτ hiid n clock t ht (hTail n),
      ← hBase]
  have hSelected :=
    AvramDividend.Classical.chat06_selected_residual_survival_of_countwise_factorisation
      N hN F hF t (ENNReal.ofReal (Real.exp (-t))) hFactor
  exact hSelected

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℕ) (hN : Measurable N)
    (clock t : ℝ) (ht : 0 ≤ t)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount : ∀ n : ℕ,
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | t < τ (N ω) ω -
      (clock - ∑ i ∈ Finset.range (N ω), τ i ω)} =
        ENNReal.ofReal (Real.exp (-t)) := by
  exact iid_random_count_residual_exp_survival
    τ hτ hiid N hN clock t ht hTail hCount
