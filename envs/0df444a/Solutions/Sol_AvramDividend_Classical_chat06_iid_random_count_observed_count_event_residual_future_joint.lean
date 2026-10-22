-- Prove2me | solution 1 for AvramDividend.Classical.chat06_iid_random_count_observed_count_event_residual_future_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:27:19.379386+00:00
-- url     : https://prove2.me/submissions/0707e8b8-2bd6-45ce-88bf-9a07d94e9534

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_count_event_residual_future_joint
import Theorems.Thm_AvramDividend_Classical_chat06_selected_past_residual_future_joint_countwise_gluing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The random-count residual and entire future waiting suffix are
jointly independent of every event measurable from the observed count. -/
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
    (C : Set ℕ) (hC : MeasurableSet C)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount : ∀ n : ℕ,
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | N ω ∈ C ∧
      t < τ (N ω) ω - (clock - ∑ i ∈ Finset.range (N ω), τ i ω) ∧
      (fun j : ℕ => τ (N ω + 1 + j) ω) ∈ B} =
        (P {ω | N ω ∈ C} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := by
  let H : Set Ω := {ω | N ω ∈ C}
  let F : ℕ → Ω → ℝ :=
    fun n ω => τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)
  let G : ℕ → Ω → (ℕ → ℝ) :=
    fun n ω j => τ (n + 1 + j) ω
  have hF (n : ℕ) : Measurable (F n) := by
    exact (hτ n).sub (measurable_const.sub
      (Finset.measurable_sum _ fun i _ => hτ i))
  have hG (n : ℕ) : Measurable (G n) := by
    apply measurable_pi_lambda
    intro j
    exact hτ (n + 1 + j)
  have hFactor (n : ℕ) :
      P {ω | ω ∈ H ∧ N ω = n ∧ t < F n ω ∧ G n ω ∈ B} =
        (P {ω | ω ∈ H ∧ N ω = n} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := by
    by_cases hn : n ∈ C
    · have hA :
          {ω | ω ∈ H ∧ N ω = n ∧ t < F n ω ∧ G n ω ∈ B} =
          {ω | N ω = n ∧ t < F n ω ∧ G n ω ∈ B} := by
        ext ω
        change (N ω ∈ C ∧ N ω = n ∧ t < F n ω ∧ G n ω ∈ B) ↔
          (N ω = n ∧ t < F n ω ∧ G n ω ∈ B)
        constructor
        · rintro ⟨_, he, hu, hb⟩
          exact ⟨he, hu, hb⟩
        · rintro ⟨he, hu, hb⟩
          exact ⟨by simpa [he] using hn, he, hu, hb⟩
      have hCeq :
          {ω | ω ∈ H ∧ N ω = n} = {ω | N ω = n} := by
        ext ω
        change (N ω ∈ C ∧ N ω = n) ↔ N ω = n
        exact ⟨And.right, fun he => ⟨by simpa [he] using hn, he⟩⟩
      rw [hA, hCeq]
      exact
        AvramDividend.Classical.chat06_indexed_count_event_residual_future_joint
          τ hτ hiid n N clock t ht μ (hLaw n) B hB (hTail n) (hCount n)
    · have hBad (ω : Ω) : ¬ (ω ∈ H ∧ N ω = n) := by
        rintro ⟨hc, he⟩
        exact hn (by simpa [H, he] using hc)
      have hA :
          {ω | ω ∈ H ∧ N ω = n ∧ t < F n ω ∧ G n ω ∈ B} =
          (∅ : Set Ω) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hBad ω ⟨h.1, h.2.1⟩
      have hCeq :
          {ω | ω ∈ H ∧ N ω = n} = (∅ : Set Ω) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hBad ω
      rw [hA, hCeq]
      simp
  simpa only [H, F, G, Set.mem_setOf_eq] using
    (AvramDividend.Classical.chat06_selected_past_residual_future_joint_countwise_gluing
      N hN H (hN hC) F hF G hG B hB t
      (ENNReal.ofReal (Real.exp (-t))) (μ B) hFactor)
