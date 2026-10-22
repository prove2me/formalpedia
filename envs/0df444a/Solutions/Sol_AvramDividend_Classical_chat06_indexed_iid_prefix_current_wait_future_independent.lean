-- Prove2me | solution 1 for AvramDividend.Classical.chat06_indexed_iid_prefix_current_wait_future_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:06:53.663397+00:00
-- url     : https://prove2.me/submissions/e0f505dc-6c4f-4008-b1c4-a716be2cab2c

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace AvramChat06

/-- The masked iid prefix together with its next wait is jointly
independent of the complete sequence strictly after that wait. -/
theorem indexed_iid_prefix_current_wait_future_independent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) :
    IndepFun
      (fun ω => ((fun i => if h : i < n then τ i ω else 0), τ n ω))
      (fun ω (j : ℕ) => τ (n + 1 + j) ω) P := by
  have hMasked :=
    AvramDividend.Classical.chat06_masked_iid_prefix_full_suffix_independence
      τ hτ hiid (n + 1)
  have hPrefix : Measurable (fun p : ℕ → ℝ =>
      fun i => if h : i < n then p i else 0) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i < n
    · simpa [hi] using
        (measurable_pi_apply i : Measurable (fun p : ℕ → ℝ => p i))
    · simp [hi]
  have hMap : Measurable (fun p : ℕ → ℝ =>
      ((fun i => if h : i < n then p i else 0), p n)) :=
    hPrefix.prodMk (measurable_pi_apply n)
  have hInd := hMasked.comp hMap measurable_id
  have h0 : IndepFun
      (fun ω => ((fun i => if h : i < n then
        (if h' : i < n + 1 then τ i ω else 0) else 0),
        (if h : n < n + 1 then τ n ω else 0)))
      (fun ω (j : ℕ) => τ (n + 1 + j) ω) P := by
    simpa only [Function.comp_def, id_eq] using hInd
  have hEq :
      (fun ω => ((fun i => if h : i < n then
        (if h' : i < n + 1 then τ i ω else 0) else 0),
        (if h : n < n + 1 then τ n ω else 0))) =
      (fun ω => ((fun i => if h : i < n then τ i ω else 0),
        τ n ω)) := by
    funext ω
    apply Prod.ext
    · funext i
      by_cases hi : i < n
      · simp [hi, Nat.lt_succ_of_lt hi]
      · simp [hi]
    · simp
  rw [hEq] at h0
  exact h0

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) :
    IndepFun
      (fun ω => ((fun i => if h : i < n then τ i ω else 0), τ n ω))
      (fun ω (j : ℕ) => τ (n + 1 + j) ω) P := by
  exact indexed_iid_prefix_current_wait_future_independent τ hτ hiid n
